module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_le_centralizer_of_forall_conj_mem {X Y : Subgroup G} {z : G}
    (hz : ∀ y ∈ Y, y⁻¹ * z * y ∈ centralizer (X : Set G)) :
    ⁅X, Y⁆ ≤ centralizer ({z} : Set G) := by
  rw [commutator_le]
  intro x hx y hy
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  have hw : x⁻¹ * (y⁻¹ * z * y) = (y⁻¹ * z * y) * x⁻¹ :=
    mem_centralizer_iff.mp (hz y hy) x⁻¹ (X.inv_mem hx)
  have hz1 : x * z = z * x := by
    have h1 := hz 1 Y.one_mem
    rw [inv_one, one_mul, mul_one] at h1
    exact mem_centralizer_iff.mp h1 x hx
  calc x * y * x⁻¹ * y⁻¹ * z = x * y * (x⁻¹ * (y⁻¹ * z * y)) * y⁻¹ := by group
    _ = x * y * ((y⁻¹ * z * y) * x⁻¹) * y⁻¹ := by rw [hw]
    _ = x * z * y * x⁻¹ * y⁻¹ := by group
    _ = z * (x * y * x⁻¹ * y⁻¹) := by rw [hz1]; group

theorem commutator_le_centralizer_of_le_normalizer {X Y : Subgroup G}
    (hn : Y ≤ normalizer ((Y ⊓ centralizer (X : Set G) : Subgroup G) : Set G)) :
    ⁅X, Y⁆ ≤ centralizer ((Y ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro z hz
  have hconj : ∀ y ∈ Y, y⁻¹ * z * y ∈ centralizer (X : Set G) := fun y hy =>
    ((mem_normalizer_iff''.mp (hn hy) z).mp hz).2
  exact (mem_centralizer_singleton_iff.mp
    (commutator_le_centralizer_of_forall_conj_mem hconj hg)).symm

structure RegularNormalData (N X E H : Subgroup G) (t : G) : Prop where
  isElementaryAbelian : IsElementaryAbelian 2 X
  sup_eq : E ⊔ zpowers t = X
  not_mem : t ∉ E
  le_normalizer_left : N ≤ normalizer (X : Set G)
  le_normalizer_right : N ≤ normalizer (E : Set G)
  le_inf_centralizer : H ≤ N ⊓ centralizer (E : Set G)
  le_closure : E ≤ closure {e | ∃ h ∈ H, ∃ c ∈ N ⊓ centralizer ({t} : Set G),
    e = c * ⁅t, h⁆ * c⁻¹}

namespace RegularNormalData

variable {N X E H : Subgroup G} {t : G} (h : RegularNormalData N X E H t)
include h

theorem le_left : E ≤ X := h.sup_eq ▸ le_sup_left

theorem mem_left : t ∈ X := h.sup_eq ▸ mem_sup_right (mem_zpowers t)

theorem mul_comm_of_mem {x y : G} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x := by
  have := h.isElementaryAbelian
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : X) ⟨y, hy⟩)

theorem mul_self : t * t = 1 := by
  have := h.isElementaryAbelian
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian t h.mem_left

theorem commute_of_mem {e : G} (he : e ∈ E) : e * t = t * e :=
  h.mul_comm_of_mem (h.le_left he) h.mem_left

theorem mem_iff {x : G} : x ∈ X ↔ x ∈ E ∨ x * t ∈ E := by
  rw [← h.sup_eq]
  exact mem_sup_zpowers_iff h.mul_self fun e he => h.commute_of_mem he

theorem conj_mem_inf_centralizer {c y : G} (hc : c ∈ N) (hy : y ∈ N ⊓ centralizer (E : Set G)) :
    c * y * c⁻¹ ∈ N ⊓ centralizer (E : Set G) := by
  refine ⟨N.mul_mem (N.mul_mem hc hy.1) (N.inv_mem hc), mem_centralizer_iff.mpr fun e he => ?_⟩
  have he' : c⁻¹ * e * c ∈ E := (mem_normalizer_iff''.mp (h.le_normalizer_right hc) e).mp he
  have hye : (c⁻¹ * e * c) * y = y * (c⁻¹ * e * c) := mem_centralizer_iff.mp hy.2 _ he'
  calc e * (c * y * c⁻¹) = c * ((c⁻¹ * e * c) * y) * c⁻¹ := by group
    _ = c * (y * (c⁻¹ * e * c)) * c⁻¹ := by rw [hye]
    _ = c * y * c⁻¹ * e := by group

theorem conj_mem_sdiff {g : G} (hg : g ∈ N) : g⁻¹ * t * g ∈ X ∧ g⁻¹ * t * g ∉ E :=
  ⟨(mem_normalizer_iff''.mp (h.le_normalizer_left hg) t).mp h.mem_left,
    fun hE => h.not_mem ((mem_normalizer_iff''.mp (h.le_normalizer_right hg) t).mpr hE)⟩

theorem crossed_mem {y : G} (hy : y ∈ N) : y⁻¹ * t * y * t ∈ E := by
  obtain ⟨hX, hE⟩ := h.conj_mem_sdiff hy
  exact (h.mem_iff.mp hX).resolve_left hE

@[expose] def crossedHom : (N ⊓ centralizer (E : Set G) : Subgroup G) →* E :=
  CFSG.EvenSmallLie.UnitarySix.YamadaD.crossedHom h.mul_self E (N ⊓ centralizer (E : Set G))
    inf_le_right fun _ hy => h.crossed_mem hy.1

theorem crossedHom_apply (y : (N ⊓ centralizer (E : Set G) : Subgroup G)) :
    (h.crossedHom y : G) = (y : G)⁻¹ * t * y * t :=
  rfl

theorem crossedHom_conj {c : G} (hc : c ∈ N ⊓ centralizer ({t} : Set G))
    (y : (N ⊓ centralizer (E : Set G) : Subgroup G)) :
    (h.crossedHom ⟨c * y * c⁻¹, h.conj_mem_inf_centralizer hc.1 y.2⟩ : G) =
      c * h.crossedHom y * c⁻¹ :=
  crossed_conj (mem_centralizer_singleton_iff.mp hc.2)

theorem commutator_eq_crossed {x : G} (hx : x ∈ H) :
    ⁅t, x⁆ = (x⁻¹)⁻¹ * t * x⁻¹ * t := by
  have hxN := (h.le_inf_centralizer hx).1
  have hconj : x * t * x⁻¹ ∈ X := (mem_normalizer_iff.mp (h.le_normalizer_left hxN) t).mp h.mem_left
  have hc := h.mul_comm_of_mem hconj h.mem_left
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.mul_self
  rw [commutatorElement_def, inv_inv, ht', hc]
  group

theorem crossedHom_surjective : Function.Surjective h.crossedHom := by
  set R : Subgroup G := h.crossedHom.range.map E.subtype
  have hsub : {e | ∃ x ∈ H, ∃ c ∈ N ⊓ centralizer ({t} : Set G), e = c * ⁅t, x⁆ * c⁻¹} ⊆
      (R : Set G) := by
    rintro e ⟨x, hx, c, hc, rfl⟩
    have hxinv : x⁻¹ ∈ N ⊓ centralizer (E : Set G) := inv_mem (h.le_inf_centralizer hx)
    refine ⟨h.crossedHom ⟨c * x⁻¹ * c⁻¹, h.conj_mem_inf_centralizer hc.1 hxinv⟩,
      ⟨_, rfl⟩, ?_⟩
    change (h.crossedHom ⟨c * x⁻¹ * c⁻¹, _⟩ : G) = _
    rw [h.crossedHom_conj hc ⟨x⁻¹, hxinv⟩, h.crossedHom_apply, h.commutator_eq_crossed hx]
  have hER : E ≤ R := h.le_closure.trans ((closure_le R).mpr hsub)
  intro e
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hER e.2
  exact ⟨y, Subtype.ext hy⟩

theorem exists_inf_centralizer_conj_eq {x : G} (hx : x ∈ X) (hxE : x ∉ E) :
    ∃ y ∈ N ⊓ centralizer (E : Set G), y⁻¹ * t * y = x := by
  have hxt : x * t ∈ E := (h.mem_iff.mp hx).resolve_left hxE
  obtain ⟨y, hy⟩ := h.crossedHom_surjective ⟨x * t, hxt⟩
  refine ⟨y, y.2, ?_⟩
  have hy' : (y : G)⁻¹ * t * y * t = x * t := by
    rw [← h.crossedHom_apply, hy]
  calc (y : G)⁻¹ * t * y = (y : G)⁻¹ * t * y * t * t := by rw [mul_assoc _ t t, h.mul_self,
        mul_one]
    _ = x := by rw [hy', mul_assoc, h.mul_self, mul_one]

end RegularNormalData

end CFSG.LocalAnalysis.EvenBN.Common
