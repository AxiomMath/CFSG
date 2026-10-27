module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinThree

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {Y K : Type} [Group Y] [Group K] {F' : Type} [Field F'] {x t : K} {J₂ J₄ : Subgroup K}
  {L : Subgroup Y} (e : K ≃* ↥L)

theorem FrameOuterQ8Free.map (h : FrameOuterQ8Free K J₂ J₄) :
    FrameOuterQ8Free ↥L ((J₂.map (L.subtype.comp e.toMonoidHom)).subgroupOf L)
      ((J₄.map (L.subtype.comp e.toMonoidHom)).subgroupOf L) := by
  intro ψ hψ h₂ h₄ q
  let ψ' : QuaternionGroup 2 →* MulAut K := (MulAut.congr e).symm.toMonoidHom.comp ψ
  have hψ' : ∀ q k, ψ' q k = e.symm (ψ q (e k)) := fun _ _ => rfl
  have hfix : ∀ {J : Subgroup K}, (∀ q, ∀ j ∈ (J.map (L.subtype.comp e.toMonoidHom)).subgroupOf L,
      ψ q j = j) → ∀ q, ∀ j ∈ J, ψ' q j = j := fun hJ q j hj => by
    rw [hψ', hJ q (e j) (Subgroup.mem_subgroupOf.mpr ⟨j, hj, rfl⟩), e.symm_apply_apply]
  obtain ⟨k, hk⟩ := h ψ' ((MulAut.congr e).symm.injective.comp hψ) (hfix h₂) (hfix h₄) q
  refine ⟨e k, MulEquiv.ext fun l => ?_⟩
  have h1 := DFunLike.congr_fun hk (e.symm l)
  rw [hψ', e.apply_symm_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, ← e.apply_symm_apply (ψ q l), h1, map_mul, map_mul, map_inv,
    e.apply_symm_apply]

namespace TwinFr

theorem coe_map_mul (a b : K) : ((e (a * b) : ↥L) : Y) = (e a : Y) * (e b : Y) := by
  rw [map_mul, Subgroup.coe_mul]

theorem map_comm_iff {a b : K} :
    (e a : Y) * (e b : Y) = (e b : Y) * (e a : Y) ↔ a * b = b * a := by
  rw [← coe_map_mul, ← coe_map_mul, Subtype.val_injective.eq_iff, e.injective.eq_iff]

theorem Frame.map (hfr : Frame (⊤ : Subgroup K) F' x t J₂ J₄) :
    Frame L F' (e x) (e t) (J₂.map (L.subtype.comp e.toMonoidHom))
      (J₄.map (L.subtype.comp e.toMonoidHom)) where
  le₂ := by rintro _ ⟨k, -, rfl⟩; exact (e k).2
  le₄ := by rintro _ ⟨k, -, rfl⟩; exact (e k).2
  mem₂ := ⟨t, hfr.mem₂, rfl⟩
  mem₄ := by rw [← coe_map_mul]; exact ⟨x * t, hfr.mem₄, rfl⟩
  orderOf_xt := by
    rw [← coe_map_mul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hfr.orderOf_xt
  ne_one := fun h => hfr.ne_one (e.injective (Subtype.ext (h.trans (by simp))))
  equiv₂ := by
    obtain ⟨φ⟩ := hfr.equiv₂
    exact ⟨(J₂.equivMapOfInjective _ (Subtype.val_injective.comp e.injective)).symm.trans φ⟩
  equiv₄ := by
    obtain ⟨φ⟩ := hfr.equiv₄
    exact ⟨(J₄.equivMapOfInjective _ (Subtype.val_injective.comp e.injective)).symm.trans φ⟩
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (map_comm_iff e).mpr (hfr.comm a ha b hb)
  cent₂ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at *
    exact (map_comm_iff e).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hfr.cent₂ ha))
  norm₂ := by
    rintro g hg hgt _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨g, hg⟩
    have hk' : (e k : Y) = g := congrArg Subtype.val hk
    subst hk'
    refine ⟨k * j * k⁻¹, hfr.norm₂ k (Subgroup.mem_top k) ((map_comm_iff e).mp hgt) j hj, ?_⟩
    simp
  norm₄ := by
    rintro g hg hgt _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨g, hg⟩
    have hk' : (e k : Y) = g := congrArg Subtype.val hk
    subst hk'
    refine ⟨k * j * k⁻¹, hfr.norm₄ k (Subgroup.mem_top k) ((map_comm_iff e).mp hgt) j hj, ?_⟩
    simp

theorem Frame3.map (hfr : Frame3 (⊤ : Subgroup K) F' x t J₂ J₄)
    (hx : ∀ g : Y, g * e x = e x * g) :
    Frame3 L F' (e x) (e t) (J₂.map (L.subtype.comp e.toMonoidHom))
      (J₄.map (L.subtype.comp e.toMonoidHom)) where
  toFrame := hfr.toFrame.map e
  card := hfr.card
  central := hx
  sq_mem := by
    rintro n hn hnt hnn
    obtain ⟨k, hk⟩ := e.surjective ⟨n, hn⟩
    have hk' : (e k : Y) = n := congrArg Subtype.val hk
    subst hk'
    rw [← coe_map_mul, Subtype.val_injective.eq_iff, e.injective.eq_iff] at hnn
    obtain ⟨b, hb, h⟩ := hfr.sq_mem k (Subgroup.mem_top k) ((map_comm_iff e).mp hnt) hnn
    refine ⟨e b, ⟨b, hb, rfl⟩, ?_⟩
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · right
      rw [coe_map_mul, coe_map_mul]
  cent_mem := by
    rintro g hg hgt hgb
    obtain ⟨k, hk⟩ := e.surjective ⟨g, hg⟩
    have hk' : (e k : Y) = g := congrArg Subtype.val hk
    subst hk'
    obtain ⟨j, hj, h⟩ := hfr.cent_mem k (Subgroup.mem_top k) ((map_comm_iff e).mp hgt)
      fun b hb hbb => (map_comm_iff e).mp (hgb (e b) ⟨b, hb, rfl⟩
        (by rw [← coe_map_mul, hbb]))
    refine ⟨e j, ⟨j, hj, rfl⟩, ?_⟩
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · right
      rw [coe_map_mul]

end TwinFr

end CFSG.ClassicalInvolution.Q3.TA3
