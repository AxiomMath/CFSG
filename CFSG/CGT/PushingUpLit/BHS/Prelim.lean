module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.CharTwoLocal
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem conjSub_iSup {ι : Sort*} (a : Γ) (H : ι → Subgroup Γ) :
    conjSub a (⨆ i, H i) = ⨆ i, conjSub a (H i) :=
  Subgroup.map_iSup _ _

theorem mem_normalizer_of_conjSub_le {a : Γ} {D : Subgroup Γ} (h1 : conjSub a D ≤ D)
    (h2 : conjSub a⁻¹ D ≤ D) : a ∈ Subgroup.normalizer (D : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 (mem_conjSub_of_mem hx)
  · intro hx
    have := h2 (mem_conjSub_of_mem hx)
    simpa [mul_assoc] using this

theorem two_two_core {G L : Subgroup Γ} (hG : CharTwo G) (hOL : pCoreOf 2 G ≤ L) (hLG : L ≤ G) :
    CharTwo L := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hG hLG hOL

theorem two_two_normalizes [Finite Γ] {G L : Subgroup Γ} (hG : CharTwo G) (hLG : L ≤ G)
    (hn : pCoreOf 2 G ≤ Subgroup.normalizer (L : Set Γ)) : CharTwo L := by
  have hJG : L ⊔ pCoreOf 2 G ≤ G :=
    sup_le hLG (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 G)
  have hJ : CharTwo (L ⊔ pCoreOf 2 G) := two_two_core hG le_sup_right hJG
  have hnorm : (L.subgroupOf (L ⊔ pCoreOf 2 G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hn)
  exact CFSG.Quasithin.CT.CharTwo.of_normal hJ le_sup_left hnorm

theorem opResidual_conjSub (p : ℕ) (m : Γ) (A : Subgroup Γ) :
    opResidual p (conjSub m A) = conjSub m (opResidual p A) := by
  unfold opResidual conjSub
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rwa [orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective] at hc
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rwa [orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective]

theorem opResidual_mono (p : ℕ) {A B : Subgroup Γ} (h : A ≤ B) : opResidual p A ≤ opResidual p B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem pow_mul_mem_of_mem_normalizer {Y : Subgroup Γ} {s y : Γ}
    (hs : s ∈ Subgroup.normalizer (Y : Set Γ)) (hy : y ∈ Y) (n : ℕ) :
    ∃ y' ∈ Y, (s * y) ^ n = s ^ n * y' := by
  induction n with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', h⟩ := ih
    have hconj : s⁻¹ * y' * s ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) y').mp hy'
      simpa using this
    refine ⟨s⁻¹ * y' * s * y, Y.mul_mem hconj hy, ?_⟩
    rw [pow_succ, h]
    group

theorem conjSub_eq_of_mem_normalizer {m : Γ} {S : Subgroup Γ}
    (hm : m ∈ Subgroup.normalizer (S : Set Γ)) : conjSub m S = S := by
  ext x
  rw [mem_conjSub_iff]
  have := (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * x * m))
  simpa [mul_assoc] using this

theorem mem_normalizer_of_conjSub_eq {m : Γ} {S : Subgroup Γ} (h : conjSub m S = S) :
    m ∈ Subgroup.normalizer (S : Set Γ) :=
  mem_normalizer_of_conjSub_le h.le (by
    have := conjSub_mono m⁻¹ h.ge
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this)

end CFSG.CGT.PushingUpLit.BHS
