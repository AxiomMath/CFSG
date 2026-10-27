module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace GammaExtra

section ThompsonSubgroup

variable {G : Type*} [Group G]

theorem isMulCommutative_iff_forall {A : Subgroup G} :
    IsMulCommutative A ↔ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  constructor
  · intro h a ha b hb
    exact congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro h
    exact ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

theorem isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  rw [Subgroup.mem_bot] at hx
  simp [hx]

theorem exists_isMaxElemAbelian [Finite G] (H : Subgroup G) : ∃ A, IsMaxElemAbelian H A := by
  obtain ⟨A, ⟨hAH, hA⟩, hmax⟩ := Set.exists_max_image {B : Subgroup G | B ≤ H ∧ IsElemAbelian 2 B}
    (fun B => Nat.card B) (Set.toFinite _) ⟨⊥, bot_le, isElemAbelian_bot⟩
  exact ⟨A, hAH, hA, fun B hBH hB => hmax B ⟨hBH, hB⟩⟩

theorem le_thompsonJ {H A : Subgroup G} (hA : IsMaxElemAbelian H A) : A ≤ thompsonJ H :=
  le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian H A) => A) A hA

theorem thompsonJ_le {H K : Subgroup G} (h : ∀ A, IsMaxElemAbelian H A → A ≤ K) :
    thompsonJ H ≤ K :=
  iSup₂_le h

theorem thompsonJ_le_self (H : Subgroup G) : thompsonJ H ≤ H :=
  thompsonJ_le fun _ hA => hA.1

theorem isPGroup_thompsonJ {S : Subgroup G} (hS : IsPGroup 2 S) : IsPGroup 2 (thompsonJ S) :=
  hS.to_le (thompsonJ_le_self S)

theorem isElemAbelian_sup_zpowers {A S : Subgroup G} (hAS : A ≤ S) (hA : IsElemAbelian 2 A) {z : G}
    (hz : ∀ s ∈ S, s * z = z * s) (hz2 : z ^ 2 = 1) :
    IsElemAbelian 2 (A ⊔ Subgroup.zpowers z) := by
  have hAc : ∀ a b, a ∈ A → b ∈ A → Commute a b := fun a b ha hb => by
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcz : ∀ a ∈ A, ∀ n : ℤ, Commute a (z ^ n) := fun a ha n =>
    Commute.zpow_right (hz a (hAS ha)) n
  have hcomm : ((A : Set G) ∪ (Subgroup.zpowers z : Set G)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hAc x y hx hy
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact hcz x hx n
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hcz y hy n).symm
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.refl z).zpow_zpow n m
  have hB : A ⊔ Subgroup.zpowers z =
      Subgroup.closure ((A : Set G) ∪ (Subgroup.zpowers z : Set G)) :=
    Subgroup.sup_eq_closure _ _
  have hBc := Subgroup.isMulCommutative_closure hcomm
  rw [hB]
  refine ⟨hBc, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA.2 x hx
    · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hBc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by rw [(Commute.mul_pow (show Commute x y from hxy) 2)]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [inv_pow, ihx, inv_one]

theorem mem_of_isMaxElemAbelian_of_central_involution [Finite G] {S A : Subgroup G}
    (hA : IsMaxElemAbelian S A) {z : G} (hzS : z ∈ S) (hz : ∀ s ∈ S, s * z = z * s)
    (hz2 : z ^ 2 = 1) : z ∈ A := by
  have hB := isElemAbelian_sup_zpowers hA.1 hA.2.1 hz hz2
  have hBS : A ⊔ Subgroup.zpowers z ≤ S := sup_le hA.1 (Subgroup.zpowers_le.mpr hzS)
  have heq : A = A ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBS hB)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem mem_thompsonJ_of_central_involution [Finite G] {S : Subgroup G} {z : G} (hzS : z ∈ S)
    (hz : ∀ s ∈ S, s * z = z * s) (hz2 : z ^ 2 = 1) : z ∈ thompsonJ S := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
  exact le_thompsonJ hA (mem_of_isMaxElemAbelian_of_central_involution hA hzS hz hz2)

theorem isElemAbelian_map_equiv_iff (f : G ≃* G) {A : Subgroup G} :
    IsElemAbelian 2 (A.map f.toMonoidHom) ↔ IsElemAbelian 2 A := by
  unfold IsElemAbelian
  rw [isMulCommutative_iff_forall, isMulCommutative_iff_forall]
  constructor
  · rintro ⟨hc, hx⟩
    refine ⟨fun a ha b hb => f.injective ?_, fun x hx' => f.injective ?_⟩
    · simpa using hc (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩
    · simpa using hx (f x) ⟨x, hx', rfl⟩
  · rintro ⟨hc, hx⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simpa [← map_mul] using congrArg f (hc a ha b hb)
    · rintro _ ⟨x, hx', rfl⟩
      simpa [← map_pow] using congrArg f (hx x hx')

theorem isMaxElemAbelian_map_equiv (f : G ≃* G) {H A : Subgroup G} (h : IsMaxElemAbelian H A) :
    IsMaxElemAbelian (H.map f.toMonoidHom) (A.map f.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, (isElemAbelian_map_equiv_iff f).mpr h.2.1, fun B hBH hB => ?_⟩
  have hB' : B.map f.symm.toMonoidHom ≤ H := by
    have := Subgroup.map_mono (f := f.symm.toMonoidHom) hBH
    rwa [map_equiv_symm_map_equiv] at this
  have hBel : IsElemAbelian 2 (B.map f.symm.toMonoidHom) :=
    (isElemAbelian_map_equiv_iff f.symm).mpr hB
  have := h.2.2 _ hB' hBel
  rw [card_map_equiv f A, ← card_map_equiv f.symm B]
  exact this

theorem thompsonJ_map_equiv (f : G ≃* G) (H : Subgroup G) :
    thompsonJ (H.map f.toMonoidHom) = (thompsonJ H).map f.toMonoidHom := by
  apply le_antisymm
  · refine thompsonJ_le fun A' hA' => ?_
    have h1 : IsMaxElemAbelian H (A'.map f.symm.toMonoidHom) := by
      have := isMaxElemAbelian_map_equiv f.symm hA'
      rwa [map_equiv_symm_map_equiv] at this
    have h2 := Subgroup.map_mono (f := f.toMonoidHom) (le_thompsonJ h1)
    rwa [map_equiv_map_equiv_symm] at h2
  · rw [Subgroup.map_le_iff_le_comap]
    refine thompsonJ_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_thompsonJ (isMaxElemAbelian_map_equiv f hA)

theorem map_conj_eq_self_of_mem_normalizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : S.map (MulAut.conj g).toMonoidHom = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)

theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y, y ∈ K ↔ g⁻¹ * y * g ∈ K := by
    intro y
    conv_lhs => rw [← h]
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have := key (g * x * g⁻¹)
  rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  exact this.symm

theorem normalizer_le_normalizer_thompsonJ (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer ((thompsonJ S : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  have := thompsonJ_map_equiv (MulAut.conj g) S
  rw [map_conj_eq_self_of_mem_normalizer hg] at this
  exact this.symm

theorem thompsonJ_eq_of_le [Finite G] {S R : Subgroup G} (hJR : thompsonJ S ≤ R) (hRS : R ≤ S) :
    thompsonJ R = thompsonJ S := by
  apply le_antisymm
  · refine thompsonJ_le fun A hA => le_thompsonJ ?_
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    have hA₀R : A₀ ≤ R := (le_thompsonJ hA₀).trans hJR
    refine ⟨hA.1.trans hRS, hA.2.1, fun B hBS hB => ?_⟩
    exact (hA₀.2.2 B hBS hB).trans (hA.2.2 A₀ hA₀R hA₀.2.1)
  · refine thompsonJ_le fun A hA => le_thompsonJ ?_
    have hAR : A ≤ R := (le_thompsonJ hA).trans hJR
    exact ⟨hAR, hA.2.1, fun B hBR hB => hA.2.2 B (hBR.trans hRS) hB⟩

end ThompsonSubgroup

end GammaExtra

end CFSG.QuasithinUnique
