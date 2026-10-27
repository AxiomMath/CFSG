
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Struct

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

theorem exists_conj_of_sylow_two {X : Type*} [Group X] [Finite X] {S T : Subgroup X}
    (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∃ g : X, S.map (MulAut.conj g).toMonoidHom = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hS.toSylow hSi) (hT.toSylow hTi)
  refine ⟨g, ?_⟩
  have h : ((g • hS.toSylow hSi : Sylow 2 X) : Set X) = ((hT.toSylow hTi : Sylow 2 X) : Set X) :=
    congrArg (fun P : Sylow 2 X => ((P : Subgroup X) : Set X)) hg
  rw [Sylow.coe_smul] at h
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (MulAut.conj g) y ∈ ((hT.toSylow hTi : Sylow 2 X) : Set X) := by
      rw [← h]
      exact Set.smul_mem_smul_set hy
    exact this
  · intro hxT
    have : x ∈ MulAut.conj g • ((hS.toSylow hSi : Sylow 2 X) : Set X) := by
      rw [h]
      exact hxT
    obtain ⟨y, hy, hyx⟩ := Set.mem_smul_set.1 this
    exact ⟨y, hy, hyx⟩

section Lift

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G}

omit [Finite G] in
theorem conj_mem_sylow_iff (hRN : R ≤ Subgroup.normalizer (L : Set G)) {r : G} (hr : r ∈ R)
    (x : ↥L) :
    ((L.normalizerMonoidHom ⟨r, hRN hr⟩ x : ↥L) : G) ∈ R ↔ (x : G) ∈ R := by
  have h1 : ((L.normalizerMonoidHom ⟨r, hRN hr⟩ x : ↥L) : G) = r * (x : G) * r⁻¹ := rfl
  rw [h1]
  constructor
  · intro h
    have := R.mul_mem (R.mul_mem (R.inv_mem hr) h) hr
    simpa [mul_assoc] using this
  · intro h
    exact R.mul_mem (R.mul_mem hr h) (R.inv_mem hr)

theorem exists_lift_local (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L)
    {X : Type} [Group X] [Finite X] (e : ↥L ≃* X) {S₀ K₀ E₀ : Subgroup X} {m : ℕ}
    (hS₀ : IsPGroup 2 S₀) (hS₀i : ¬ 2 ∣ S₀.index)
    (hinv : ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ → K₀.map α.toMonoidHom = K₀)
    (hmax : ∀ Y : Subgroup X, K₀ ≤ Y → Y = K₀ ∨ Y = ⊤)
    (hstruct : Alt2Struct K₀ E₀ m) (hs : IsSimpleGroup (alternatingGroup (Fin m)))
    (hn : ¬ IsPGroup 2 (alternatingGroup (Fin m)))
    (hm : Nat.card (alternatingGroup (Fin m)) = 360 ∨ Nat.card (alternatingGroup (Fin m)) = 2520) :
    ∃ K : Subgroup G, K ≤ L ∧ R ≤ Subgroup.normalizer (K : Set G) ∧ CharTwo K ∧
      ¬ HasChi0Block K ∧ IsAltOverElemAbelian K 4 m ∧
      ∀ Y : Subgroup G, K ≤ Y → Y ≤ L → Y = K ∨ Y = L := by
  classical
  set S : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSdef
  have hS2 : IsPGroup 2 S := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSi : ¬ 2 ∣ S.index := hS.2.2
  have hS'2 : IsPGroup 2 (S.map e.toMonoidHom) := hS2.map e.toMonoidHom
  have hS'i : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact hSi
  obtain ⟨g, hg⟩ := exists_conj_of_sylow_two hS₀ hS₀i hS'2 hS'i
  let φ : X ≃* ↥L := (MulAut.conj g).trans e.symm
  have hφS : S₀.map φ.toMonoidHom = S := by
    have h1 : S₀.map φ.toMonoidHom =
        (S₀.map (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hg, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id ↥L := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  let f : X →* G := L.subtype.comp φ.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp φ.injective
  have hstruct' := hstruct.map f hf
  have hrange : f.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ y).2
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [f]⟩
  refine ⟨K₀.map f, ?_, ?_, hstruct'.charTwo hs hn, hstruct'.not_hasChi0Block hs hm,
    hstruct'.isAltOver, ?_⟩
  · intro x hx
    obtain ⟨k, -, rfl⟩ := hx
    exact (φ k).2
  · intro r hr
    have hrN : r ∈ Subgroup.normalizer (L : Set G) := hRN hr
    set c : MulAut ↥L := L.normalizerMonoidHom ⟨r, hrN⟩ with hc
    have hcx : ∀ x : ↥L, ((c x : ↥L) : G) = r * (x : G) * r⁻¹ := fun x => rfl
    set α : MulAut X := φ.trans (c.trans φ.symm) with hα
    have hαf : ∀ k : X, f (α k) = r * f k * r⁻¹ := by
      intro k
      show ((φ (φ.symm (c (φ k))) : ↥L) : G) = r * ((φ k : ↥L) : G) * r⁻¹
      rw [MulEquiv.apply_symm_apply]
      exact hcx _
    have hSc : S.map c.toMonoidHom = S := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : G) ∈ R ⊓ L := hx
        have : ((c x : ↥L) : G) ∈ R ⊓ L := ⟨(conj_mem_sylow_iff hRN hr x).2 hx'.1, (c x).2⟩
        exact this
      · intro hy
        have hy' : (y : G) ∈ R ⊓ L := hy
        refine ⟨c.symm y, ?_, by simp⟩
        have h1 : ((c (c.symm y) : ↥L) : G) ∈ R := by simpa using hy'.1
        show ((c.symm y : ↥L) : G) ∈ R ⊓ L
        exact ⟨(conj_mem_sylow_iff hRN hr (c.symm y)).1 h1, (c.symm y).2⟩
    have hαS : S₀.map α.toMonoidHom = S₀ := by
      have h1 : S₀.map α.toMonoidHom = ((S₀.map φ.toMonoidHom).map c.toMonoidHom).map
          φ.symm.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      rw [h1, hφS, hSc, ← hφS, Subgroup.map_map]
      have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    have hK := hinv α hαS
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨α k, ?_, hαf k⟩
      rw [← hK]
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k', hk', hk'x⟩
      rw [← hK] at hk'
      obtain ⟨k, hk, rfl⟩ := hk'
      refine ⟨k, hk, ?_⟩
      have h2 : r * f k * r⁻¹ = r * x * r⁻¹ := by rw [← hαf k]; exact hk'x
      have h3 := mul_left_cancel (mul_right_cancel h2)
      exact h3
  · intro Y hKY hYL
    have hle : K₀ ≤ Y.comap f := by
      intro k hk
      exact hKY ⟨k, hk, rfl⟩
    have hYf : (Y.comap f).map f = Y := by
      rw [Subgroup.map_comap_eq, hrange]
      exact inf_of_le_right hYL
    rcases hmax _ hle with h1 | h1
    · left
      rw [← hYf, h1]
    · right
      rw [← hYf, h1, Subgroup.map_top, hrange]

end Lift

end CFSG.QuasithinUnique.Vol2Native.L239
