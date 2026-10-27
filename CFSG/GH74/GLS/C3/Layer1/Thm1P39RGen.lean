module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Aux
public import CFSG.GH74.GLS.SP.Local.SPLCtW
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Thm1End
public import CFSG.GH74.GLS.C3.Layer1.Thm1Notation
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

variable {G : Type} [Group G]

theorem conj_mem_zCenter {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) {u : G}
    (hu : u ∈ zCenter H) : g * u * g⁻¹ ∈ zCenter H := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg u).1 hu.1, fun h hh => ?_⟩
  have hh' : g⁻¹ * h * g ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (H : Set G)).inv_mem hg) h).1 hh
    simpa using this
  have h1 := hu.2 _ hh'
  calc h * (g * u * g⁻¹) = g * ((g⁻¹ * h * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
    _ = g * u * g⁻¹ * h := by group

theorem le_thompsonJ2 {T A : Subgroup G} (hA : A ≤ T) (hel : IsElementaryAbelian 2 ↥A)
    (hmax : ∀ B : Subgroup G, B ≤ T → IsElementaryAbelian 2 ↥B → Nat.card ↥B ≤ Nat.card ↥A) :
    A ≤ thompsonJ2 T :=
  le_iSup₂_of_le A ⟨hA, hel, hmax⟩ le_rfl

theorem map_conj_le_of_mem_normalizer {T A : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G))
    (hA : A ≤ T) : A.map (MulAut.conj g).toMonoidHom ≤ T := by
  rintro _ ⟨a, ha, rfl⟩
  have := (Subgroup.mem_normalizer_iff.1 hg a).1 (hA ha)
  simpa [MulAut.conj_apply] using this

theorem thompsonJ2_conj_le {T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G)) :
    (thompsonJ2 T).map (MulAut.conj g).toMonoidHom ≤ thompsonJ2 T := by
  have hg' : g⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hg
  unfold thompsonJ2
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  obtain ⟨hAT, hel, hmax⟩ := hA
  have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine le_thompsonJ2 (map_conj_le_of_mem_normalizer hg hAT) ?_ ?_
  · have := hel
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  · intro B hBT hBel
    have hB' := map_conj_le_of_mem_normalizer hg' hBT
    have := hBel
    have hel' : IsElementaryAbelian 2 ↥(B.map (MulAut.conj g⁻¹).toMonoidHom) :=
      IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom
    have h1 := hmax _ hB' hel'
    have h2 : Nat.card ↥(B.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥B :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [hcard]
    omega

theorem conj_mem_thompsonJ2 {T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G)) {u : G}
    (hu : u ∈ thompsonJ2 T) : g * u * g⁻¹ ∈ thompsonJ2 T := by
  have := thompsonJ2_conj_le hg ⟨u, hu, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem conj_mem_closure {S : Set G} {g : G} (hS : ∀ u ∈ S, g * u * g⁻¹ ∈ S) {w : G}
    (hw : w ∈ Subgroup.closure S) : g * w * g⁻¹ ∈ Subgroup.closure S := by
  induction hw using Subgroup.closure_induction with
  | mem u hu => exact Subgroup.subset_closure (hS u hu)
  | one => simp
  | mul u v _ _ hu hv =>
    have := (Subgroup.closure S).mul_mem hu hv
    simpa [mul_assoc] using this
  | inv u _ hu =>
    have := (Subgroup.closure S).inv_mem hu
    simpa [mul_assoc] using this

theorem mem_three_cases {z f x w : G} (hz : z * z = 1) (hf : f * f = 1) (hx : x * x = 1)
    (hzf : z * f = f * z) (hzx : z * x = x * z) (hfx : f * x = x * f)
    (hw : w ∈ zpowers z ⊔ zpowers f ⊔ zpowers x) :
    (w = 1 ∨ w = z ∨ w = f ∨ w = z * f) ∨ (w = x ∨ w = z * x ∨ w = f * x ∨ w = z * f * x) := by
  have hcomm : ∀ u ∈ zpowers z ⊔ zpowers f, ∀ v ∈ zpowers x, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hv
    have hux : u * x = x * u := by
      rcases Thm1G33.klein_cases hz hf hzf hu with rfl | rfl | rfl | rfl
      · simp
      · exact hzx
      · exact hfx
      · calc z * f * x = z * (f * x) := mul_assoc _ _ _
          _ = z * (x * f) := by rw [hfx]
          _ = (z * x) * f := (mul_assoc _ _ _).symm
          _ = (x * z) * f := by rw [hzx]
          _ = x * (z * f) := mul_assoc _ _ _
    exact (Commute.zpow_right (show Commute u x from hux) i).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hw
  have hv' := Thm1P310.eq_one_or_eq_of_mem_zpowers hx hv
  rcases Thm1G33.klein_cases hz hf hzf hu with rfl | rfl | rfl | rfl <;>
    rcases hv' with rfl | rfl
  · exact Or.inl (Or.inl (by simp))
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (Or.inr (Or.inl (by simp)))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (by simp))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by simp))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem exists_fixed_f₁ {x f z a : G} (hz : z * z = 1) (hf : f * f = 1) (hx : x * x = 1)
    (hzf : z * f = f * z) (hzx : z * x = x * z) (hfx : f * x = x * f)
    (hz1 : z ≠ 1) (hf1 : f ≠ 1) (hfz : f ≠ z) (hfx' : f ≠ x) (hfzx : f ≠ z * x)
    (haA : a * f * a⁻¹ ∈ zpowers z ⊔ zpowers f ⊔ zpowers x)
    (hax : a * x * a⁻¹ = x * z) (haz : a * z * a⁻¹ = z)
    (ha2 : a * (a * f * a⁻¹) * a⁻¹ = f) :
    ∃ f₁, (f₁ = f ∨ f₁ = f * x) ∧ a * f₁ * a⁻¹ = f₁ := by
  have hzx3 : ∀ y : G, z * (x * y) = x * (z * y) := fun y => by
    rw [← mul_assoc, hzx, mul_assoc]
  have hzf3 : ∀ y : G, z * (f * y) = f * (z * y) := fun y => by
    rw [← mul_assoc, hzf, mul_assoc]
  have hzz3 : ∀ y : G, z * (z * y) = y := fun y => by rw [← mul_assoc, hz, one_mul]
  have hxx3 : ∀ y : G, x * (x * y) = y := fun y => by rw [← mul_assoc, hx, one_mul]
  have hmul : ∀ g h : G, a * (g * h) * a⁻¹ = (a * g * a⁻¹) * (a * h * a⁻¹) := fun g h => by group
  have hxz : x * z = z * x := hzx.symm
  rcases mem_three_cases hz hf hx hzf hzx hfx haA with (h | h | h | h) | (h | h | h | h)
  · exfalso; apply hf1
    rw [h] at ha2
    rw [← ha2]; group
  · exfalso; apply hfz
    rw [h] at ha2
    exact ha2.symm.trans haz
  · exact ⟨f, Or.inl rfl, h⟩
  · refine ⟨f * x, Or.inr rfl, ?_⟩
    rw [hmul, h, hax]
    simp only [mul_assoc, hzf3, hzx3, hz, mul_one]
  · exfalso; apply hfzx
    rw [h, hax] at ha2
    rw [← ha2, hxz]
  · exfalso; apply hfx'
    rw [h, hmul, haz, hax] at ha2
    rw [← ha2]
    simp only [hzx3, hz, mul_one]
  · exfalso; apply hz1
    rw [h, hmul, h, hax] at ha2
    have h1 : f * z = f * 1 := by
      calc f * z = f * x * (x * z) := by simp only [mul_assoc, hxx3]
        _ = f := ha2
        _ = f * 1 := (mul_one f).symm
    exact mul_left_cancel h1
  · exfalso; apply hz1
    rw [h, hmul, hmul, haz, h, hax] at ha2
    have h1 : f * z = f * 1 := by
      calc f * z = z * (z * f * x) * (x * z) := by
            simp only [mul_assoc, hzz3, hxx3, hzf3]
        _ = f := ha2
        _ = f * 1 := (mul_one f).symm
    exact mul_left_cancel h1

def dihedralCast {a b : ℕ} (h : a = b) : DihedralGroup a ≃* DihedralGroup b := by
  subst h; exact MulEquiv.refl _

theorem exists_dihedral_equiv {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hP : IsDihedralTwoGroup ↥P n) : Nonempty (↥P ≃* DihedralGroup (2 ^ (n - 1))) := by
  obtain ⟨-, k, hk, -, ⟨e⟩⟩ := hP
  have hk' : k = 2 ^ (n - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  exact ⟨e.trans (dihedralCast hk')⟩

theorem not_isCyclic_of_isDihedralMaxIn {P₀ P : Subgroup G} (h : IsDihedralMaxIn P₀ P) :
    ¬ IsCyclic ↥P₀ := by
  obtain ⟨-, -, k, -, hk2, ⟨e⟩⟩ := h
  intro hc
  exact Proofs2.not_isCyclic_dihedral hk2 (isCyclic_of_surjective e.toMonoidHom e.surjective)

theorem eq_of_isDihedralMaxIn_three {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hP : IsDihedralTwoGroup ↥P n) {A B C : Subgroup G} (hA : IsDihedralMaxIn A P)
    (hB : IsDihedralMaxIn B P) (hC : IsDihedralMaxIn C P) : A = B ∨ B = C ∨ A = C := by
  obtain ⟨e⟩ := exists_dihedral_equiv hn hP
  have hcardP : Nat.card ↥P = Nat.card (DihedralGroup (2 ^ (n - 1))) := Nat.card_congr e.toEquiv
  have hcard : ∀ {M : Subgroup G}, IsDihedralMaxIn M P →
      Nat.card ↥(M.comap (C3.Layer1.P34.PShape.embed P e)) * 2 =
        Nat.card (DihedralGroup (2 ^ (n - 1))) := by
    intro M hM
    rw [C3.Layer1.P34.PShape.card_comap P e hM.1, ← hcardP, hM.2.1]
    ring
  have hnc : ∀ {M : Subgroup G}, IsDihedralMaxIn M P →
      ¬ IsCyclic ↥(M.comap (C3.Layer1.P34.PShape.embed P e)) := fun hM =>
    C3.Layer1.P34.PShape.not_isCyclic_comap P e hM.1 (not_isCyclic_of_isDihedralMaxIn hM)
  rcases C3.Layer1.P34.PShape.max_a (hcard hA) (hcard hB) (hcard hC) (hnc hA) (hnc hB) (hnc hC)
    with h | h | h
  · exact Or.inl (C3.Layer1.P34.PShape.comap_inj P e hA.1 hB.1 h)
  · exact Or.inr (Or.inl (C3.Layer1.P34.PShape.comap_inj P e hB.1 hC.1 h))
  · exact Or.inr (Or.inr (C3.Layer1.P34.PShape.comap_inj P e hA.1 hC.1 h))

theorem exists_isDihedralMaxIn {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hP : IsDihedralTwoGroup ↥P n) : ∃ P₀ : Subgroup G, IsDihedralMaxIn P₀ P := by
  obtain ⟨e⟩ := exists_dihedral_equiv hn hP
  have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hk'2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  let e' : ↥P ≃* DihedralGroup (2 * 2 ^ (n - 2)) := e.trans (dihedralCast h2)
  let ι : DihedralGroup (2 * 2 ^ (n - 2)) →* G := P.subtype.comp e'.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e'.symm.injective
  refine ⟨(SP.Local.CtW.Bsub (2 ^ (n - 2))).map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact (e'.symm g).2
  · have hcP : Nat.card ↥P = 2 * (2 * 2 ^ (n - 2)) := by
      rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
    rw [hcP, Subgroup.card_map_of_injective hι, SP.Local.CtW.card_Bsub hk'2]
  · have hcard : Nat.card ↥((SP.Local.CtW.Bsub (2 ^ (n - 2))).map ι) = 2 * 2 ^ (n - 2) := by
      rw [Subgroup.card_map_of_injective hι, SP.Local.CtW.card_Bsub hk'2]
    obtain ⟨eB⟩ := SP.Local.CtW.Bsub_equiv hk'2
    exact ⟨2 ^ (n - 2), hcard, hk'2,
      ⟨(Subgroup.equivMapOfInjective _ ι hι).symm.trans eB⟩⟩

variable [Finite G]

theorem exists_sylow_ne {x : G} {T : Subgroup G} (hTp : IsPGroup 2 ↥T) (hx2 : orderOf x = 2)
    (hxT : x ∈ T) (hxc : ∀ t ∈ T, t * x = x * t) (hnc : ¬ CFSG.GH74.IsCentralInvolution x) :
    ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ T ≤ S ∧ T ≠ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS, -, hSp, hSidx⟩ := C3.Layer1.P34.exists_sylow_ge (N := (⊤ : Subgroup G)) (K := T)
    le_top hTp
  have hSsyl : IsSylowOf 2 S ⊤ := isSylowOf_iff.2 ⟨le_top, hSp, hSidx⟩
  refine ⟨S, hSsyl, hTS, fun h => hnc ?_⟩
  have hSidx' : ¬ 2 ∣ S.index := by
    have := hSsyl.isPGroup
    rwa [Subgroup.relIndex_top_right] at hSidx
  subst h
  exact Thm1.isCentralInvolution_of_mem_center_sylow hSp hSidx' hxT hxc hx2

theorem exists_a₀ {T S : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hTS : T ≤ S) (hne : T ≠ S) :
    ∃ a : G, a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T := by
  obtain ⟨b, hbS, hbN, hbT⟩ := Thm1G33.exists_mem_normalizer_not_mem hTS hne hS2
  have hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hS2 ⟨b, hbS⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨c, hc, hcT, hc2⟩ := Thm1G33.exists_pow_not_mem_sq_mem hb2 hbT
  refine ⟨c, ?_, ?_, hcT, hc2⟩
  · exact (zpowers_le.2 hbS) hc
  · exact (zpowers_le.2 hbN) hc

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
