module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusAmbient

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Equivariance

variable {X : Type} [Group X]

theorem normalizer_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    normalizer ((H.map φ.toMonoidHom : Subgroup X) : Set X) =
      (normalizer (H : Set X)).map φ.toMonoidHom :=
  (Subgroup.map_normalizer_eq_of_bijective H φ.bijective).symm

theorem map_inf_mulEquiv (φ : X ≃* X) (H K : Subgroup X) :
    (H ⊓ K).map φ.toMonoidHom = H.map φ.toMonoidHom ⊓ K.map φ.toMonoidHom :=
  Subgroup.map_inf_eq _ _ _ φ.injective

theorem oddCoreOf_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    oddCoreOf (H.map φ.toMonoidHom) = (oddCoreOf H).map φ.toMonoidHom :=
  pPrimeCoreOf_map_mulEquiv φ H

theorem pTwoCoreOf_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    pTwoCoreOf (H.map φ.toMonoidHom) = (pTwoCoreOf H).map φ.toMonoidHom := by
  let ψ : ↥H ≃* ↥(H.map φ.toMonoidHom) := Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective
  have h1 : (pCore 2 ↥H).map ψ.toMonoidHom = pCore 2 ↥(H.map φ.toMonoidHom) :=
    pCore_map_iso 2 ψ
  have h2 : (H.map φ.toMonoidHom).subtype.comp ψ.toMonoidHom = φ.toMonoidHom.comp H.subtype := by
    ext g; rfl
  unfold pTwoCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem oddTwoCoreOf_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    oddTwoCoreOf (H.map φ.toMonoidHom) = (oddTwoCoreOf H).map φ.toMonoidHom := by
  let ψ : ↥H ≃* ↥(H.map φ.toMonoidHom) := Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective
  have h1 : (pPrimeCore 2 ↥H).map ψ.toMonoidHom = pPrimeCore 2 ↥(H.map φ.toMonoidHom) :=
    pPrimeCore_map_iso 2 ψ
  let ψb : (↥H ⧸ pPrimeCore 2 ↥H) ≃*
      (↥(H.map φ.toMonoidHom) ⧸ pPrimeCore 2 ↥(H.map φ.toMonoidHom)) :=
    QuotientGroup.congr _ _ ψ h1
  have h3 : (pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).map ψb.toMonoidHom =
      pCore 2 (↥(H.map φ.toMonoidHom) ⧸ pPrimeCore 2 ↥(H.map φ.toMonoidHom)) :=
    pCore_map_iso 2 ψb
  have hmk : ∀ h : ↥H, ψb (QuotientGroup.mk h) = QuotientGroup.mk (ψ h) := fun h =>
    QuotientGroup.congr_mk _ _ _ _ h
  ext x
  constructor
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨h, rfl⟩ := ψ.surjective h'
    have hh : (QuotientGroup.mk h : ↥H ⧸ pPrimeCore 2 ↥H) ∈ pCore 2 (↥H ⧸ pPrimeCore 2 ↥H) := by
      have : ψb (QuotientGroup.mk h) ∈ pCore 2 (↥(H.map φ.toMonoidHom) ⧸
          pPrimeCore 2 ↥(H.map φ.toMonoidHom)) := by rw [hmk]; exact hh'
      rw [← h3] at this
      obtain ⟨q, hq, hq'⟩ := Subgroup.mem_map.1 this
      have := ψb.injective hq'
      rw [← this]
      exact hq
    exact ⟨(h : X), ⟨h, hh, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨ψ h, ?_, rfl⟩
    show (QuotientGroup.mk (ψ h) : _) ∈ pCore 2 _
    rw [← hmk, ← h3]
    exact Subgroup.mem_map_of_mem _ hh

theorem mem_map_mulEquiv_iff (φ : X ≃* X) (K : Subgroup X) (x : X) :
    φ x ∈ K.map φ.toMonoidHom ↔ x ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem mem_normalizer_map_iff (φ : X ≃* X) (K : Subgroup X) (x : X) :
    φ x ∈ normalizer ((K.map φ.toMonoidHom : Subgroup X) : Set X) ↔
      x ∈ normalizer (K : Set X) := by
  rw [normalizer_map_mulEquiv, mem_map_mulEquiv_iff]

theorem mem_centralizerSection_map (φ : X ≃* X) (K M : Subgroup X) (x : X) :
    φ x ∈ centralizerSection (K.map φ.toMonoidHom) (M.map φ.toMonoidHom) ↔
      x ∈ centralizerSection K M := by
  show (φ x ∈ normalizer ((K.map φ.toMonoidHom : Subgroup X) : Set X) ∧
      φ x ∈ normalizer ((M.map φ.toMonoidHom : Subgroup X) : Set X) ∧
      ∀ k ∈ K.map φ.toMonoidHom, ⁅k, φ x⁆ ∈ M.map φ.toMonoidHom) ↔
    (x ∈ normalizer (K : Set X) ∧ x ∈ normalizer (M : Set X) ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ M)
  rw [mem_normalizer_map_iff, mem_normalizer_map_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h k hk
    have := h (φ k) ((mem_map_mulEquiv_iff φ K k).2 hk)
    rw [← map_commutatorElement] at this
    exact (mem_map_mulEquiv_iff φ M _).1 this
  · intro h k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    have h1 : ⁅φ.toMonoidHom k₀, φ x⁆ = φ ⁅k₀, x⁆ := (map_commutatorElement φ k₀ x).symm
    rw [h1]
    exact (mem_map_mulEquiv_iff φ M _).2 (h k₀ hk₀)

theorem zStar_map_mulEquiv (φ : X ≃* X) (H : Subgroup X) :
    zStar (H.map φ.toMonoidHom) = (zStar H).map φ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [mem_map_mulEquiv_iff]
  show (φ x ∈ H.map φ.toMonoidHom ∧
      φ x ∈ centralizerSection (H.map φ.toMonoidHom) (pPrimeCoreOf 2 (H.map φ.toMonoidHom))) ↔
    (x ∈ H ∧ x ∈ centralizerSection H (pPrimeCoreOf 2 H))
  rw [pPrimeCoreOf_map_mulEquiv, mem_centralizerSection_map, mem_map_mulEquiv_iff]

theorem IsSylowTwoIn.map_mulEquiv {W Q : Subgroup X} (h : IsSylowTwoIn W Q) (φ : X ≃* X) :
    IsSylowTwoIn (W.map φ.toMonoidHom) (Q.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Subgroup.map_mono h1, ?_, ?_⟩
  · exact h2.of_equiv (Subgroup.equivMapOfInjective Q φ.toMonoidHom φ.injective)
  · rwa [Subgroup.relIndex_map_map_of_injective _ _ φ.injective]

end Equivariance

section Transport

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def normalizerEquiv (φ : X ≃* X) (Z : Subgroup X) :
    ↥(normalizer (Z : Set X)) ≃* ↥(normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)) :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (normalizer_map_mulEquiv φ Z).symm)

theorem Sec5Data.map {n : ℕ} {z : X} {Z : Subgroup X}
    {S : Sylow 2 ↥(normalizer (Z : Set X))} (h : Sec5Data X n z Z S) (φ : X ≃* X) :
    ∃ S' : Sylow 2 ↥(normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)),
      Sec5Syl S' = (Sec5Syl S).map φ.toMonoidHom ∧
        Sec5Data X n (φ z) (Z.map φ.toMonoidHom) S' := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := normalizerEquiv φ Z
  let S' : Sylow 2 ↥(normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hN := normalizer_map_mulEquiv φ Z
  have hK0 : K0 X n (normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)) =
      (K0 X n (normalizer (Z : Set X))).map φ.toMonoidHom := by
    rw [hN, K0_map]
  have hS' : Sec5Syl S' = (Sec5Syl S).map φ.toMonoidHom := by
    show ((S : Subgroup ↥(normalizer (Z : Set X))).map e.toMonoidHom).map
        (normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)).subtype =
      ((S : Subgroup ↥(normalizer (Z : Set X))).map (normalizer (Z : Set X)).subtype).map
        φ.toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨S', hS', h.cex, h.hypA, h.maxdeg, ?_, ?_⟩
  ·
    have hK : K0 X n (centralizer ({φ z} : Set X)) =
        (K0 X n (centralizer ({z} : Set X))).map φ.toMonoidHom := by
      rw [centralizer_singleton_map_mulEquiv, K0_map]
    refine ⟨by rw [MulEquiv.orderOf_eq]; exact h.orderOf_z, Subgroup.mem_map_of_mem _ h.z_mem, ?_⟩
    rw [hK, zStar_map_mulEquiv]
    exact h.pair.sylow.map_mulEquiv φ
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    ·
      refine ⟨?_, ?_⟩
      · rw [hK0, pTwoCoreOf_map_mulEquiv]
        exact congrArg (Subgroup.map φ.toMonoidHom) h.l52.a.1
      · rw [hK0, oddTwoCoreOf_map_mulEquiv]
        exact h.l52.a.2.map_mulEquiv φ
    ·
      intro s' hs' hs'2 hcomm
      rw [hN] at hs'
      obtain ⟨s, hsN, rfl⟩ := Subgroup.mem_map.1 hs'
      have hs2 : orderOf s = 2 := by
        have : orderOf (φ.toMonoidHom s) = orderOf s := MulEquiv.orderOf_eq φ s
        rw [← this]; exact hs'2
      have hcomm' : ∀ k ∈ K0 X n (normalizer (Z : Set X)),
          ⁅k, s⁆ ∈ pPrimeCoreOf 2 (K0 X n (normalizer (Z : Set X))) := by
        intro k hk
        have h1 := hcomm (φ k) (by rw [hK0]; exact (mem_map_mulEquiv_iff φ _ k).2 hk)
        rw [hK0, pPrimeCoreOf_map_mulEquiv] at h1
        have h2 : ⁅φ k, φ s⁆ = φ ⁅k, s⁆ := (map_commutatorElement φ k s).symm
        exact (mem_map_mulEquiv_iff φ _ _).1 (h2 ▸ h1)
      have hb := h.l52.b s hsN hs2 hcomm'
      have hb' := congrArg (Subgroup.map φ.toMonoidHom) hb
      have hcen : (centralizer ({s} : Set X)).map φ.toMonoidHom =
          centralizer ({φ.toMonoidHom s} : Set X) := (centralizer_singleton_map_mulEquiv φ s).symm
      rw [Subgroup.map_sup, map_inf_mulEquiv, ← oddCoreOf_map_mulEquiv, hcen, ← hN] at hb'
      exact hb'
    ·
      intro s' hs' hs'2 hne
      rw [hN] at hs'
      obtain ⟨s, hsN, rfl⟩ := Subgroup.mem_map.1 hs'
      have hs2 : orderOf s = 2 := by
        have : orderOf (φ.toMonoidHom s) = orderOf s := MulEquiv.orderOf_eq φ s
        rw [← this]; exact hs'2
      have hne' : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)) ≠ ⊥ := by
        intro hbot
        apply hne
        have h1 : K0 X n (normalizer ((Z.map φ.toMonoidHom : Subgroup X) : Set X)) ⊓
            centralizer ({φ.toMonoidHom s} : Set X) =
            (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({s} : Set X)).map φ.toMonoidHom := by
          rw [hK0, map_inf_mulEquiv]
          exact congrArg (fun H => (K0 X n (normalizer (Z : Set X))).map φ.toMonoidHom ⊓ H)
            (centralizer_singleton_map_mulEquiv φ s)
        rw [h1, ← K0_map, hbot, Subgroup.map_bot]
      have hc := h.l52.c s hsN hs2 hne'
      have hc' := congrArg (Subgroup.map φ.toMonoidHom) hc
      have hL : (LPlusIn (centralizer ({s} : Set X))).map φ.toMonoidHom =
          LPlusIn (centralizer ({φ.toMonoidHom s} : Set X)) := by
        rw [LPlusIn_map_of_injective _ φ.toMonoidHom φ.injective,
          ← centralizer_singleton_map_mulEquiv]
        rfl
      rw [Subgroup.map_sup, map_inf_mulEquiv, hL, ← hN, ← pPrimeCoreOf_map_mulEquiv, hL] at hc'
      exact hc'
    ·
      have hd := h.l52.d.map_mulEquiv φ
      rw [Subgroup.map_top_of_surjective _ φ.surjective] at hd
      show IsSylowTwoIn ⊤ (Sec5Syl S')
      rw [hS']
      exact hd
    ·
      intro heq
      apply h.l52.e
      have heq' : {x : X | x ∈ (Sec5Syl S).map φ.toMonoidHom ∧
          ∃ g : X, g⁻¹ * x * g ∈ Z.map φ.toMonoidHom} =
          ((Z.map φ.toMonoidHom : Subgroup X) : Set X) := by
        rw [← hS']
        exact heq
      ext x
      have hx := Set.ext_iff.1 heq' (φ x)
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe] at hx
      show (x ∈ Sec5Syl S ∧ ∃ g : X, g⁻¹ * x * g ∈ Z) ↔ x ∈ Z
      constructor
      · rintro ⟨hxS, g, hg⟩
        have hφ : φ x ∈ Z.map φ.toMonoidHom := hx.1 ⟨(mem_map_mulEquiv_iff φ _ x).2 hxS, φ g, by
          have : (φ g)⁻¹ * φ x * φ g = φ (g⁻¹ * x * g) := by simp
          rw [this]
          exact (mem_map_mulEquiv_iff φ Z _).2 hg⟩
        exact (mem_map_mulEquiv_iff φ Z x).1 hφ
      · intro hxZ
        have hφ : φ x ∈ Z.map φ.toMonoidHom := (mem_map_mulEquiv_iff φ Z x).2 hxZ
        obtain ⟨hxS', -⟩ := hx.2 hφ
        exact ⟨(mem_map_mulEquiv_iff φ _ x).1 hxS', 1, by simpa using hxZ⟩

theorem Sec5Data.mirror {n : ℕ} {z : X} {Z : Subgroup X}
    {S : Sylow 2 ↥(normalizer (Z : Set X))} (h : Sec5Data X n z Z S) (g : X) :
    ∃ S' : Sylow 2 ↥(normalizer ((Z.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup X) : Set X)),
      Sec5Data X n (g⁻¹ * z * g) (Z.map (MulAut.conj g⁻¹).toMonoidHom) S' := by
  obtain ⟨S', -, hS'⟩ := h.map (MulAut.conj g⁻¹)
  have hz : (MulAut.conj g⁻¹) z = g⁻¹ * z * g := by simp
  rw [hz] at hS'
  exact ⟨S', hS'⟩

end Transport

end CFSG.OddStandard.Solomon75
