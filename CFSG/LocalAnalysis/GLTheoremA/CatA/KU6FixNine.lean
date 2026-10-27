module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6FixLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Lift
import CFSG.Holt.H78.Lemma16Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Fix

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.KU6Cent CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open Module Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (mem_primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 hF4_bar bar bar_bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

private abbrev gm (g : Gu) : Matrix (Fin 6) (Fin 6) F4 := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

private theorem gm_mul_mulVec (g h : Gu) (v : Fin 6 → F4) :
    gm (g * h) *ᵥ v = gm g *ᵥ (gm h *ᵥ v) :=
  (Matrix.mulVec_mulVec v (gm g) (gm h)).symm

private theorem gm_one_mulVec (v : Fin 6 → F4) : gm 1 *ᵥ v = v := Matrix.one_mulVec v

private theorem gm_inv_mulVec (g : Gu) (v : Fin 6 → F4) : gm g⁻¹ *ᵥ (gm g *ᵥ v) = v := by
  rw [← gm_mul_mulVec, inv_mul_cancel, gm_one_mulVec]

private theorem gm_mulVec_inv (g : Gu) (v : Fin 6 → F4) : gm g *ᵥ (gm g⁻¹ *ᵥ v) = v := by
  rw [← gm_mul_mulVec, mul_inv_cancel, gm_one_mulVec]

theorem scalar_mem_Gu (c : F4ˣ) : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Gu := by
  rw [mem_primeFormUnitary]
  have hn := norm_units c
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm] at hn
  have hd : ((Matrix.diagonal fun _ : Fin 6 => (c : F4)).map hF4.bar) =
      Matrix.diagonal fun _ : Fin 6 => hF4.bar (c : F4) :=
    Matrix.diagonal_map (map_zero _)
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hd, Matrix.diagonal_transpose,
    idGram, Units.val_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal, mul_comm, hn,
    Matrix.diagonal_one]

noncomputable def scalG : F4ˣ →* Gu :=
  MonoidHom.codRestrict (Matrix.GeneralLinearGroup.scalar (Fin 6)) Gu scalar_mem_Gu

theorem ZG_eq_range : ZG = scalG.range := by
  ext g
  rw [mem_ZG, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem card_ZG : Nat.card ZG = 3 := by
  have hinj : Function.Injective scalG := by
    intro c d h
    have h' := congrArg (fun g : Gu => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) 0 0) h
    simp [scalG, Matrix.GeneralLinearGroup.scalar] at h'
    exact Units.ext h'
  rw [ZG_eq_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units,
    Nat.card_eq_fintype_card, F4.card]

theorem ZG_comm {z : Gu} (hz : z ∈ ZG) (x : Gu) : x * z = z * x := by
  obtain ⟨c, hc⟩ := mem_ZG.1 hz
  have hcen : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Subgroup.center (GL (Fin 6) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  apply Subtype.ext
  have h := (Subgroup.mem_center_iff.1 hcen) (x : GL (Fin 6) F4)
  rw [hc] at h
  exact h

private def fixV (H : Subgroup Gu) : Submodule F4 (Fin 6 → F4) where
  carrier := {v | ∀ t ∈ H, gm t *ᵥ v = v}
  add_mem' {a b} ha hb t ht := by
    change gm t *ᵥ (a + b) = a + b
    rw [Matrix.mulVec_add, ha t ht, hb t ht]
  zero_mem' t _ := Matrix.mulVec_zero _
  smul_mem' c v hv t ht := by
    change gm t *ᵥ (c • v) = c • v
    rw [Matrix.mulVec_smul, hv t ht]

private theorem mem_fixV {H : Subgroup Gu} {v : Fin 6 → F4} : v ∈ fixV H ↔ ∀ t ∈ H, gm t *ᵥ v = v :=
  Iff.rfl

private theorem mulVec_mem_hperp {W : Submodule F4 (Fin 6 → F4)} {g : Gu}
    (hg : ∀ w ∈ W, gm g⁻¹ *ᵥ w ∈ W) {y : Fin 6 → F4} (hy : y ∈ hperp W) : gm g *ᵥ y ∈ hperp W := by
  rw [mem_hperp] at hy ⊢
  intro w hw
  have h1 := hy _ (hg w hw)
  rw [← hf_mulVec g, gm_mulVec_inv] at h1
  exact h1

@[instance_reducible]
private def nzAct {G : Type} [Group G] (ρ : G →* Gu) (W : Submodule F4 (Fin 6 → F4))
    (hW : ∀ g, ∀ w ∈ W, gm (ρ g) *ᵥ w ∈ W) :
    MulAction G {w : Fin 6 → F4 // w ∈ W ∧ w ≠ 0} where
  smul g w := ⟨gm (ρ g) *ᵥ w.1, hW g w.1 w.2.1, fun h => w.2.2 (by
    have h1 := gm_inv_mulVec (ρ g) w.1
    rw [h, Matrix.mulVec_zero] at h1
    exact h1.symm)⟩
  one_smul w := Subtype.ext (by
    change gm (ρ 1) *ᵥ w.1 = w.1
    rw [map_one, gm_one_mulVec])
  mul_smul g h w := Subtype.ext (by
    change gm (ρ (g * h)) *ᵥ w.1 = gm (ρ g) *ᵥ (gm (ρ h) *ᵥ w.1)
    rw [map_mul, gm_mul_mulVec])

private theorem card_nonzero (W : Submodule F4 (Fin 6 → F4)) :
    Nat.card {w : Fin 6 → F4 // w ∈ W ∧ w ≠ 0} = 4 ^ finrank F4 W - 1 := by
  classical
  let e : {w : Fin 6 → F4 // w ∈ W ∧ w ≠ 0} ≃ {x : W | x ≠ 0} :=
    { toFun := fun w => ⟨⟨w.1, w.2.1⟩, fun h => w.2.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.1.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Set.card_ne_eq, ← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := F4), Nat.card_eq_fintype_card (α := F4), F4.card]

private theorem not_two_dvd_four_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : ¬ 2 ∣ 4 ^ k - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem false_of_nine (A : Subgroup (MulAut S6)) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (T : Subgroup S6) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hAT : ∀ α ∈ A, ∀ x ∈ T, α x ∈ T)
    (B : Gu) {c : F4ˣ} (hc : c ≠ 1)
    (hBc : (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hBA : Psi0 B ∈ A) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : Gu →* PGU6 := QuotientGroup.mk' ZG with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective ZG
  have hk : Nat.card π.ker = 3 := by rw [hπ, QuotientGroup.ker_mk']; exact card_ZG
  have hcen : ∀ z ∈ π.ker, ∀ x : Gu, x * z = z * x := by
    intro z hz x
    rw [hπ, QuotientGroup.ker_mk'] at hz
    exact ZG_comm hz x
  set Ah : Subgroup Gu := (A.comap Psi).comap π with hAh
  have hmemAh : ∀ g : Gu, g ∈ Ah ↔ Psi0 g ∈ A := fun g => Iff.rfl
  have hAr : A ≤ Psi.range := by
    intro α hα
    obtain ⟨g, hg⟩ := exists_Psi_of_pow_three α (hA.2 α hα)
    exact ⟨g, hg⟩
  have hAhcard : 81 ≤ Nat.card Ah := by
    have h1 : Nat.card (A.comap Psi) = Nat.card A := by
      rw [← Subgroup.card_map_of_injective Psi_injective, Subgroup.map_comap_eq, inf_eq_right.2 hAr]
    rw [hAh, CatB.InnU6.card_comap_of_surjective hπs, hk, h1]
    omega
  have hAh9 : ∀ g ∈ Ah, g ^ 9 = 1 := by
    intro g hg
    have h3 : Psi0 (g ^ 3) = 1 := by rw [map_pow]; exact hA.2 _ ((hmemAh g).1 hg)
    obtain ⟨z, hz⟩ := (Psi0_eq_one_iff _).1 h3
    apply Subtype.ext
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, Subgroup.coe_pow, ← hz, ← map_pow, units_cube,
      map_one, OneMemClass.coe_one]
  have hAhp : IsPGroup 3 Ah := fun g => ⟨2, Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hAh9 g g.2)⟩
  have hN : ∀ e ∈ A.comap Psi, ∀ t ∈ T.map iota, e * t * e⁻¹ ∈ T.map iota := by
    intro e he t ht
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ht
    rw [← iota_Psi0]
    exact ⟨Psi0 g x, hAT _ he x hx, rfl⟩
  have hTi : T.map iota ≠ ⊥ := fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T iota_injective).1 h)
  obtain ⟨T₀, hT₀, hT₀1, hNT₀⟩ := CatB.InnU6.exists_two_normal hπs hk hcen (hT.map iota) hTi hN
  set C := fixV T₀ with hC
  set D := hperp C with hD
  set R := C ⊓ D with hR
  have hCAh : ∀ p ∈ Ah, ∀ v ∈ C, gm p *ᵥ v ∈ C := by
    intro p hp v hv t ht
    have h1 : p⁻¹ * t * p ∈ T₀ := by
      have h2 := hNT₀ p⁻¹ (inv_mem hp) t ht
      rwa [inv_inv] at h2
    have h2 : t * p = p * (p⁻¹ * t * p) := by group
    rw [← gm_mul_mulVec, h2, gm_mul_mulVec, mem_fixV.1 hv _ h1]
  have hDAh : ∀ p ∈ Ah, ∀ v ∈ D, gm p *ᵥ v ∈ D := fun p hp v hv =>
    mulVec_mem_hperp (fun w hw => hCAh p⁻¹ (inv_mem hp) w hw) hv
  have hRAh : ∀ p ∈ Ah, ∀ v ∈ R, gm p *ᵥ v ∈ R := fun p hp v hv =>
    ⟨hCAh p hp v hv.1, hDAh p hp v hv.2⟩
  have hRR : R ≤ hperp R := by
    intro y hy
    rw [mem_hperp]
    intro x hx
    exact (mem_hperp.1 hy.2) x hx.1
  have hDT₀ : ∀ t : T₀, ∀ w ∈ D, gm (T₀.subtype t) *ᵥ w ∈ D := fun t w hw =>
    mulVec_mem_hperp (fun u hu => by
      change gm ((t : Gu)⁻¹) *ᵥ u ∈ C
      rw [mem_fixV.1 hu _ (inv_mem t.2)]
      exact hu) hw
  have hCtop : C ≠ ⊤ := by
    intro htop
    apply hT₀1
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    apply Subtype.ext
    apply Units.ext
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have hv : v ∈ C := by rw [htop]; exact Submodule.mem_top
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (mem_fixV.1 hv t ht).trans (Matrix.one_mulVec v).symm
  have hD1 : 1 ≤ finrank F4 D := by
    have h1 := Submodule.finrank_lt hCtop
    rw [Module.finrank_fin_fun] at h1
    rw [hD, finrank_hperp]
    omega
  obtain ⟨r, hr0, hrR⟩ : ∃ r : Fin 6 → F4, r ≠ 0 ∧ r ∈ R := by
    letI := nzAct T₀.subtype D hDT₀
    have hnd : ¬ 2 ∣ Nat.card {w : Fin 6 → F4 // w ∈ D ∧ w ≠ 0} := by
      rw [card_nonzero]
      exact not_two_dvd_four_pow_sub_one hD1
    obtain ⟨x, hx⟩ := hT₀.nonempty_fixed_point_of_prime_not_dvd_card _ hnd
    refine ⟨x.1, x.2.2, ?_, x.2.1⟩
    intro t ht
    have h1 := congrArg Subtype.val (hx ⟨t, ht⟩)
    exact h1
  have hBAh : B ∈ Ah := hBA
  have hcycR : cyc (gm B) r ≤ R := cyc_le (hRAh B hBAh) hrR
  have hR3 : finrank F4 R = 3 := by
    have h1 := Submodule.finrank_mono hcycR
    rw [finrank_cyc hc hBc hr0] at h1
    have h2 := finrank_le_three hRR
    omega
  have hcomZ : ∀ g ∈ Ah, g * B * g⁻¹ * B⁻¹ ∈ ZG := by
    intro g hg
    have hg' := (hmemAh g).1 hg
    have hcomm : Psi0 g * Psi0 B = Psi0 B * Psi0 g :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hg'⟩ ⟨_, hBA⟩)
    have h1 : Psi0 (g * B * g⁻¹ * B⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    obtain ⟨z, hz⟩ := (Psi0_eq_one_iff _).1 h1
    exact mem_ZG.2 ⟨z, hz⟩
  let φ : Ah →* Gu := MonoidHom.mk' (fun g => (g : Gu) * B * (g : Gu)⁻¹ * B⁻¹) (fun g h => by
    have ha := ZG_comm (hcomZ g g.2)
    have hb := ZG_comm (hcomZ h h.2)
    simp only [Subgroup.coe_mul]
    calc (g : Gu) * h * B * ((g : Gu) * h)⁻¹ * B⁻¹ =
        ((g : Gu) * ((h : Gu) * B * (h : Gu)⁻¹ * B⁻¹)) * (B * (g : Gu)⁻¹ * B⁻¹) := by group
      _ = (((h : Gu) * B * (h : Gu)⁻¹ * B⁻¹) * g) * (B * (g : Gu)⁻¹ * B⁻¹) := by rw [hb]
      _ = ((h : Gu) * B * (h : Gu)⁻¹ * B⁻¹) * ((g : Gu) * B * (g : Gu)⁻¹ * B⁻¹) := by group
      _ = ((g : Gu) * B * (g : Gu)⁻¹ * B⁻¹) * ((h : Gu) * B * (h : Gu)⁻¹ * B⁻¹) := ha _)
  have hφ : ∀ g : Ah, φ g = (g : Gu) * B * (g : Gu)⁻¹ * B⁻¹ := fun _ => rfl
  have hrange : Nat.card φ.range ≤ 3 := by
    rw [← card_ZG]
    apply Subgroup.card_le_of_le
    rintro _ ⟨g, rfl⟩
    exact hcomZ g g.2
  set K := φ.ker with hK
  set ρ : K →* Gu := Ah.subtype.comp K.subtype with hρ
  have hρB : ∀ k : K, ρ k * B = B * ρ k := by
    intro k
    have h1 : φ k = 1 := k.2
    rw [hφ] at h1
    change ((k : Ah) : Gu) * B = B * ((k : Ah) : Gu)
    calc ((k : Ah) : Gu) * B = ((k : Ah) : Gu) * B * ((k : Ah) : Gu)⁻¹ * B⁻¹ * (B * (k : Ah)) := by
          group
      _ = B * ((k : Ah) : Gu) := by rw [h1, one_mul]
  have hRK : ∀ k : K, ∀ w ∈ R, gm (ρ k) *ᵥ w ∈ R := fun k w hw =>
    hRAh _ (k : Ah).2 w hw
  letI := nzAct ρ R hRK
  have hfree : ∀ (k : K) (x : {w : Fin 6 → F4 // w ∈ R ∧ w ≠ 0}), k • x = x → k = 1 := by
    intro k x hx
    have hx1 : gm (ρ k) *ᵥ x.1 = x.1 := congrArg Subtype.val hx
    have hcomm : gm (ρ k) * gm B = gm B * gm (ρ k) := by
      have h1 := congrArg (fun g : Gu => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) (hρB k)
      exact h1
    have hfix := fix_cyc hcomm hx1
    have hW := (cyc_le (hRAh B hBAh) x.2.1)
    have hWW : cyc (gm B) x.1 ≤ hperp (cyc (gm B) x.1) :=
      hW.trans (hRR.trans (Submodule.orthogonalBilin_le hW))
    have h1 : ρ k = 1 := eq_one_of_fix (ρ k) (hAh9 _ (k : Ah).2) hWW (finrank_cyc hc hBc x.2.2) hfix
    have hinj : Function.Injective ρ := Ah.subtype_injective.comp K.subtype_injective
    exact hinj (h1.trans (map_one ρ).symm)
  have hdvd : Nat.card K ∣ 63 := by
    have h1 := CFSG.Holt.H78.L16.natCard_dvd_natCard_of_free hfree
    rwa [card_nonzero, hR3] at h1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hAhp.to_subgroup K)
  have hK9 : Nat.card K ≤ 9 := by
    rw [hn] at hdvd ⊢
    by_contra hlt
    have h3 : 3 ≤ n := by
      by_contra h
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h27 : 3 ^ 3 ∣ 63 := (pow_dvd_pow 3 h3).trans hdvd
    norm_num at h27
  have hidx := Subgroup.card_mul_index K
  rw [hK, Subgroup.index_ker] at hidx
  have : Nat.card Ah ≤ 27 := by
    rw [← hidx]
    calc Nat.card φ.ker * Nat.card φ.range ≤ 9 * 3 := Nat.mul_le_mul hK9 hrange
      _ = 27 := by norm_num
  omega

end CFSG.LocalAnalysis.GLTheoremA.KU6Fix

end
