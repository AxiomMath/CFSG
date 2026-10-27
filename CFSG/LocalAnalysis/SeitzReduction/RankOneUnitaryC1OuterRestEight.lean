module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem outerRest_exists_centralizing_of_eight
    (hcf : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) (hf : f = 3)
    (htrY : ∀ b ∈ szA₁ (szT₁ L T), ∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G),
      outerRestPt t k y = b) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ normalizer (szR (szT₁ L T) V t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), outerRestPt t k x = b := by
  classical
  have hYT : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (szT₁ L T : Set G) :=
    fun n hn => (hcf.normalizer_szR_le h hS2 hk hn).2.2.1
  have hYA : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) :=
    fun n hn => normalizer_le_normalizer_inf_centralizer _ (hYT hn)
  have hY8 := (hcf.outerRest_card_le h hS2 hk
    (H := normalizer (szR (szT₁ L T) V t : Set G)) le_rfl).2 htrY
  obtain ⟨E, _, _, _, σ, hEcard, hσ, hfix, u, v, hc, hA₁u⟩ := h.exists_rootCoords_of_card_sylow hS2
  subst hf
  set Y := normalizer (szR (szT₁ L T) V t : Set G) with hYdef
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set T₁ := szT₁ L T with hT₁
  have : Fintype E := Fintype.ofFinite E
  have hE64 : Nat.card E = 64 := by rw [hEcard]; norm_num
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul]
    have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hE64] at h1
    exact h1
  let Zs : AddSubgroup E :=
    { carrier := {x | σ x = x}
      add_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
        show σ (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero σ
      neg_mem' := fun {a} (ha : σ a = a) => by
        show σ (-a) = -a
        rw [map_neg, ha] }
  have hZ8 : Nat.card Zs = 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← hfix]
    rfl
  set ι : Zs →+ E := Zs.subtype with hι
  have hιinj : Function.Injective ι := Zs.subtype_injective
  have hNmem : ∀ a : E, σ (a * σ a) = a * σ a := fun a => by rw [map_mul, hσσ, mul_comm]
  let Nm : E → Zs := fun a => ⟨a * σ a, hNmem a⟩
  have hNm : ∀ a, ι (Nm a) = a ^ 9 := fun a => by
    change a * σ a = a ^ 9
    rw [hσ]
    ring
  have hA₁T : ∀ b ∈ A₁, b ∈ T₁ := fun b hb => szA₁_le _ hb
  have hvZ : ∀ b ∈ A₁, σ (v b) = v b := fun b hb =>
    hc.sigma_v_of_u_eq_zero (hA₁T b hb) ((hA₁u b (hA₁T b hb)).mp hb)
  let w : A₁ → Multiplicative Zs := fun b => Multiplicative.ofAdd ⟨v b, hvZ b b.2⟩
  have hwmul : ∀ b b' : A₁, w (b * b') = w b * w b' := fun b b' => by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change v ((b : G) * b') = v b + v b'
    exact hc.v_mul_of_u_eq_zero (hA₁T b b.2) (hA₁T b' b'.2) ((hA₁u b (hA₁T b b.2)).mp b.2)
  have hwbij : Function.Bijective w := by
    refine ⟨fun b b' hbb => Subtype.ext ?_, fun z => ?_⟩
    · have h1 : v b = v b' :=
        congrArg (fun z : Multiplicative Zs => ((Multiplicative.toAdd z : Zs) : E)) hbb
      exact hc.inj _ (hA₁T b b.2) _ (hA₁T b' b'.2)
        (by rw [(hA₁u b (hA₁T b b.2)).mp b.2, (hA₁u b' (hA₁T b' b'.2)).mp b'.2]) h1
    · have hz : σ ((Multiplicative.toAdd z : Zs) : E) = (Multiplicative.toAdd z : Zs) :=
        (Multiplicative.toAdd z).2
      obtain ⟨y, hyT, hyu, hyv⟩ := hc.surj 0 _ (by
        rw [hz, zero_mul, add_zero]
        exact CharTwo.add_self_eq_zero _)
      have hyA : y ∈ A₁ := (hA₁u y hyT).mpr hyu
      refine ⟨⟨y, hyA⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      exact Subtype.ext hyv
  let c : A₁ ≃* Multiplicative Zs := MulEquiv.ofBijective (MonoidHom.mk' w hwmul) hwbij
  let ψ : Y →* MulAut A₁ := A₁.normalizerMonoidHom.comp (inclusion hYA)
  let lam : Y →* Multiplicative (AddAut Zs) :=
    (MulAutMultiplicative Zs).toMonoidHom.comp ((MulAut.congr c).toMonoidHom.comp ψ)
  have hlam : ∀ (n : Y) (b : G) (hb : b ∈ A₁),
      ((Multiplicative.toAdd (lam n) ⟨v b, hvZ b hb⟩ : Zs) : E) = v ((n : G) * b * (n : G)⁻¹) := by
    intro n b hb
    have hcb : c.symm (Multiplicative.ofAdd ⟨v b, hvZ b hb⟩) = ⟨b, hb⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change ((Multiplicative.toAdd (c (ψ n (c.symm (Multiplicative.ofAdd ⟨v b, hvZ b hb⟩)))) : Zs) :
      E) = _
    rw [hcb]
    rfl
  have hcompat : ∀ g ∈ lam.range, ∃ φ : AddAut E, ∀ a,
      Multiplicative.toAdd g (Nm a) = Nm (φ a) := by
    rintro _ ⟨n, rfl⟩
    have hnT : (n : G) ∈ normalizer (T₁ : Set G) := hYT n.2
    have hnA₁ : ∀ y ∈ T₁, y ∈ A₁ → (n : G) * y * (n : G)⁻¹ ∈ A₁ := fun y _ hy =>
      (mem_normalizer_iff.mp (hYA n.2) y).mp hy
    have hconjT : ∀ y ∈ T₁, (n : G) * y * (n : G)⁻¹ ∈ T₁ := fun y hy =>
      (mem_normalizer_iff.mp hnT y).mp hy
    obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hnT
      (fun y hy hu => (hA₁u _ (hconjT y hy)).mp (hnA₁ y hy ((hA₁u y hy).mpr hu)))
      (fun y hy hu => (hA₁u y hy).mp (by
        have h1 := (hA₁u _ (hconjT y hy)).mpr hu
        have h2 := (mem_normalizer_iff.mp (hYA n.2) y).mpr h1
        exact h2))
    refine ⟨φ, fun a => ?_⟩
    obtain ⟨y, hyT, rfl⟩ := hc.u_surj a
    have hy2T : y ^ 2 ∈ T₁ := pow_mem hyT 2
    obtain ⟨hy2u, hy2v⟩ := hc.sq hyT
    have hy2A : y ^ 2 ∈ A₁ := (hA₁u _ hy2T).mpr hy2u
    have hNmy : Nm (u y) = ⟨v (y ^ 2), hvZ _ hy2A⟩ := Subtype.ext hy2v.symm
    obtain ⟨hz2u, hz2v⟩ := hc.sq (hconjT y hyT)
    apply Subtype.ext
    rw [hNmy, hlam n _ hy2A]
    change v ((n : G) * y ^ 2 * (n : G)⁻¹) = φ (u y) * σ (φ (u y))
    rw [← hφ y hyT, ← hz2v]
    congr 1
    rw [sq, sq]
    group
  have hdvd21 : Nat.card lam.range ∣ 21 :=
    card_dvd_21_of_norm_equivariant (by rw [hE64]) hZ8 ι hιinj Nm hNm lam.range hcompat
  have hker : ∀ n : Y, lam n = 1 → ∀ b ∈ A₁, (n : G) * b * (n : G)⁻¹ = b := by
    intro n hn b hb
    have hψ : ψ n = 1 := by
      have h1 : (MulAut.congr c) (ψ n) = 1 := (MulAutMultiplicative Zs).injective (by
        rw [map_one]
        exact hn)
      exact (MulAut.congr c).injective (by rw [h1, map_one])
    have h1 := congrArg (fun φ : MulAut A₁ => ((φ ⟨b, hb⟩ : A₁) : G)) hψ
    exact h1
  set S : Subgroup Y := (Y ⊓ outerRestStab L T V t).subgroupOf Y with hSdef
  have hSidx : S.index = 8 := by
    have h1 := S.card_mul_index
    rw [hSdef, Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_left : Y ⊓ outerRestStab L T V t ≤ Y)).toEquiv] at h1
    have hpos : 0 < Nat.card (Y ⊓ outerRestStab L T V t : Subgroup G) := Nat.card_pos
    have h2 : Nat.card (Y ⊓ outerRestStab L T V t : Subgroup G) * S.index =
        Nat.card (Y ⊓ outerRestStab L T V t : Subgroup G) * 8 := by
      rw [h1, hY8]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hK : lam.ker.index ∣ 21 := by rw [Subgroup.index_ker]; exact hdvd21
  have hsup : lam.ker ⊔ S = ⊤ := by
    have h1 : (lam.ker ⊔ S).index ∣ lam.ker.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (lam.ker ⊔ S).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_right
    have h3 : (lam.ker ⊔ S).index ∣ Nat.gcd 21 8 := Nat.dvd_gcd (h1.trans hK) (hSidx ▸ h2)
    rw [show Nat.gcd 21 8 = 1 by norm_num, Nat.dvd_one] at h3
    exact Subgroup.index_eq_one.mp h3
  intro b hb
  obtain ⟨y, hyY, hyb⟩ := htrY b hb
  have hmem : ((⟨y, hyY⟩ : Y) : Y) ∈ ((lam.ker ⊔ S : Subgroup Y) : Set Y) := by
    rw [hsup]; exact mem_top _
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨k', hk', s, hs, hks⟩ := Set.mem_mul.mp hmem
  have hsS : (s : G) ∈ outerRestStab L T V t := (mem_inf.mp (mem_subgroupOf.mp hs)).2
  have hs1 := ((hcf.mem_outerRestStab_iff h hS2 hk).mp hsS).2
  have hkA := hker k' hk'
  have hy : (k' : G) * s = y := congrArg Subtype.val hks
  refine ⟨k', mem_inf.mpr ⟨k'.2, mem_centralizer_iff.mpr fun b' hb' => ?_⟩, ?_⟩
  · calc b' * (k' : G) = (k' : G) * b' * (k' : G)⁻¹ * k' := by rw [hkA b' hb']
      _ = (k' : G) * b' := by group
  · rw [← hyb, ← hy, hcf.outerRestPt_mul h hS2 hk k'.2 s.2, hs1]
    group

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
