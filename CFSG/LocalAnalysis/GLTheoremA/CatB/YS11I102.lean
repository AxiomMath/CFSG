module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineU
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Matrix

section Transport

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_inner {X L A : Subgroup G} (hL : GLAPComponent 3 X L) (hA : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hinn : ∀ a ∈ A, InducesInnerMod 3 L a)
    {B : ℕ} (hB : ∀ F : Subgroup (PSimple 3 L), IsElemAbelian 3 F → Nat.card F ≤ B) :
    Nat.card A ≤ B * Nat.card ↥(A ⊓ centModSubgroup 3 L) := by
  haveI : Group.IsPerfect (PQuot 3 L) := ⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).1⟩
  have hZ : Subgroup.center (PSimple 3 L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (PQuot 3 L)
  have hκ : Function.Injective (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center (PSimple 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut (PSimple 3 L) => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  let ψ : A →* MulAut (PSimple 3 L) := (chevAut 3 L).comp (Subgroup.inclusion hAN)
  have hψ : ∀ a : A, ψ a ∈ (MulAut.conj : PSimple 3 L →* MulAut (PSimple 3 L)).range := by
    intro a
    have h1 := (inducesInnerMod_iff_barAut_mem_inner (p := 3) (hAN a.2)).1 (hinn a a.2)
    exact CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_inner_le h1
  let ρ : A →* PSimple 3 L :=
    (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ψ.codRestrict _ hψ)
  have hker : ∀ x : A, ρ x = 1 ↔ (x : G) ∈ centModSubgroup 3 L := by
    intro x
    have h1 : ρ x = 1 ↔ ψ x = 1 := by
      show (MonoidHom.ofInjective hκ).symm (ψ.codRestrict _ hψ x) = 1 ↔ ψ x = 1
      rw [MulEquiv.map_eq_one_iff]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have h3 : chevAut 3 L (Subgroup.inclusion hAN x) = 1 ↔
        CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L (Subgroup.inclusion hAN x) = 1 := by
      constructor
      · intro h
        apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
          (PQuot 3 L)
        rw [map_one]
        exact h
      · intro h
        show CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (PQuot 3 L) _ = 1
        rw [h, map_one]
    exact h1.trans (Iff.trans Iff.rfl (h3.trans ((chev_barAut_eq_one_iff_centMod (hAN x.2)).trans
      centMod_iff)))
  have hker_card : Nat.card ρ.ker = Nat.card ↥(A ⊓ centModSubgroup 3 L) := by
    have he : ρ.ker = (A ⊓ centModSubgroup 3 L).subgroupOf A := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker x, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [he]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hR : IsElemAbelian 3 ρ.range := by
    haveI := hA.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := ρ.mem_range.1 x.2
      obtain ⟨b, hb⟩ := ρ.mem_range.1 y.2
      apply Subtype.ext
      show (x : PSimple 3 L) * (y : PSimple 3 L) = (y : PSimple 3 L) * (x : PSimple 3 L)
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm' a b]
    · obtain ⟨a, ha⟩ := ρ.mem_range.1 hx
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (a : G) a.2)
      rw [← ha, ← map_pow, ha3, map_one]
  have hcard := Subgroup.card_ker_mul_card_range ρ
  have hr : Nat.card ρ.range ≤ B := hB _ hR
  rw [← hcard, hker_card]
  calc Nat.card ↥(A ⊓ centModSubgroup 3 L) * Nat.card ρ.range
      ≤ Nat.card ↥(A ⊓ centModSubgroup 3 L) * B := Nat.mul_le_mul_left _ hr
    _ = B * Nat.card ↥(A ⊓ centModSubgroup 3 L) := mul_comm _ _

end Transport

theorem card_le_81_gl8 {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 8)
    (H : Subgroup (GL ι (ZMod 2))) (hH : IsElemAbelian 3 H) : Nat.card H ≤ 81 := by
  haveI := hH.1
  have h := Rank3.card_le_three_pow_of_injective' (E := ↥H) (fun a b => mul_comm' a b)
    (fun e => Subtype.ext (by simpa using hH.2 (e : GL ι (ZMod 2)) e.2))
    H.subtype Subtype.val_injective
  rw [hι] at h
  simpa using h

theorem card_le_81_d4 {S : Type} [Group S] (h : catalogIs S S9.isD4two) {F : Subgroup S}
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 81 := by
  obtain ⟨e⟩ := bridge_d4two h
  have hF' : IsElemAbelian 3
      ((F.map e.toMonoidHom).map CFSG.AGLEmbedding.Om8.subtype) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hF _) _
  have hcard : Nat.card ((F.map e.toMonoidHom).map CFSG.AGLEmbedding.Om8.subtype) = Nat.card F := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective e.injective]
  rw [← hcard]
  exact card_le_81_gl8 (by simp) _ hF'

theorem card_le_81_sl5 (E : Subgroup (GL (Fin 5) K4)) (hE : IsElemAbelian 3 E)
    (hdet : ∀ g ∈ E, (g : Matrix (Fin 5) (Fin 5) K4).det = 1) : Nat.card E ≤ 81 := by
  haveI := hE.1
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := fun a b => mul_comm' a b }
  have hE3 : ∀ e : E, e ^ 3 = 1 := fun e => Subtype.ext (by simpa using hE.2 (e : GL (Fin 5) K4) e.2)
  let ρE : E →* Module.End (ZMod 2) (Fin 5 → K4) := (glRepZ 5).comp E.subtype
  have hcomm : ∀ (e : E) (a : K4ˣ), Commute (ρE e) (scalRep 5 a) := by
    intro e a
    apply LinearMap.ext
    intro x
    simp [ρE, glRepZ_apply, scalRep_apply, Matrix.mulVec_smul, Module.End.mul_apply]
  let ρP : (E × K4ˣ) →* Module.End (ZMod 2) (Fin 5 → K4) :=
    ρE.noncommCoprod (scalRep 5) hcomm
  have hρP : ∀ p : E × K4ˣ, ρP p = ρE p.1 * scalRep 5 p.2 := fun p => rfl
  have hP3 : ∀ p : E × K4ˣ, p ^ 3 = 1 := fun p =>
    Prod.ext (by simp [hE3]) (by simp [K4_unit_cube])
  have hfaith : ∀ (g : E) (a : K4ˣ), ρE g * scalRep 5 a = 1 → g = 1 ∧ a = 1 := by
    intro g a h
    have hx : ∀ x : Fin 5 → K4,
        ((g : GL (Fin 5) K4) : Matrix (Fin 5) (Fin 5) K4) *ᵥ ((a : K4) • x) = x := by
      intro x
      have := congrArg (fun φ : Module.End (ZMod 2) (Fin 5 → K4) => φ x) h
      simpa [ρE, glRepZ_apply, scalRep_apply] using this
    have hmat : ((g : GL (Fin 5) K4) : Matrix (Fin 5) (Fin 5) K4) =
        ((a⁻¹ : K4ˣ) : K4) • (1 : Matrix (Fin 5) (Fin 5) K4) := by
      ext i j
      have h1 := congrFun (hx (Pi.single j 1)) i
      simp only [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply] at h1
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      by_cases hij : i = j
      · subst hij
        simp at h1 ⊢
        exact (eq_inv_of_mul_eq_one_right h1)
      · simp [hij] at h1 ⊢
        exact h1
    have hd := hdet (g : GL (Fin 5) K4) g.2
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
    have hu5 : (a⁻¹) ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd)
    have ha : a⁻¹ = 1 := (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 5 3)).1
      ⟨hu5, K4_unit_cube _⟩
    have ha1 : a = 1 := inv_eq_one.1 ha
    refine ⟨Subtype.ext (Units.ext ?_), ha1⟩
    rw [hmat, ha]
    simp
  have hfix : Rank3.fixSub ρP ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    rw [Rank3.mem_fixSub] at hp
    have h1 : ρE p.1 * scalRep 5 p.2 = 1 := by
      apply LinearMap.ext
      intro x
      have := hp x Submodule.mem_top
      rw [hρP] at this
      simpa using this
    obtain ⟨h2, h3⟩ := hfaith _ _ h1
    rw [Subgroup.mem_bot]
    exact Prod.ext h2 h3
  have hle : Nat.card (E × K4ˣ) ≤ 3 ^ (Module.finrank (ZMod 2) (Fin 5 → K4) / 2) := by
    have h := Rank3.index_fixSub_le hP3 ρP _ ⊤ rfl (fun _ _ _ => Submodule.mem_top)
    rw [hfix, Subgroup.index_bot, finrank_top] at h
    exact h
  rw [Nat.card_prod, K4_card_units, finrank_pi_K4] at hle
  have h5 : Nat.card E * 3 ≤ 3 ^ 5 := by simpa using hle
  omega

theorem card_le_81_u5 {S : Type} [Group S] (h : catalogIs S S9.isU5two) {F : Subgroup S}
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 81 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.bridge_u5two_stated h
  let e2 : S ≃* StatedSU 5 (2 ^ 1) K4 :=
    e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv CFSG.Fischer.F4.equivGaloisField 5 (2 ^ 1))
  have hF' : IsElemAbelian 3 ((F.map e2.toMonoidHom).map (StatedSU 5 (2 ^ 1) K4).subtype) :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hF _) _
  have hcard : Nat.card ((F.map e2.toMonoidHom).map (StatedSU 5 (2 ^ 1) K4).subtype) =
      Nat.card F := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective e2.injective]
  have hdet : ∀ g ∈ (F.map e2.toMonoidHom).map (StatedSU 5 (2 ^ 1) K4).subtype,
      (g : Matrix (Fin 5) (Fin 5) K4).det = 1 := by
    intro g hg
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact (mem_statedSU_K4 (by norm_num) y.2).1
  rw [← hcard]
  exact card_le_81_sl5 _ hF' hdet

theorem i102InnAt_of_u6
    (hU6 : ∀ (S : Type) [Group S], catalogIs S S9.isU6two → ∀ F : Subgroup S,
      IsElemAbelian 3 F → Nat.card F ≤ 81)
    (G : Type) [Group G] [Finite G] : I102InnAt G := by
  intro X L A hL hcat hA hAN hinn
  have hB : ∀ F : Subgroup (PSimple 3 L), IsElemAbelian 3 F → Nat.card F ≤ 81 := by
    intro F hF
    obtain ⟨i, hi, he⟩ := hcat
    rcases hi with h4 | h5 | h6
    · exact card_le_81_d4 (S := PSimple 3 L) ⟨i, h4, he⟩ hF
    · exact card_le_81_u5 (S := PSimple 3 L) ⟨i, h5, he⟩ hF
    · exact hU6 (PSimple 3 L) ⟨i, h6, he⟩ F hF
  have h := card_le_of_inner hL hA hAN hinn hB
  have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
  rw [h81]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.CatB
