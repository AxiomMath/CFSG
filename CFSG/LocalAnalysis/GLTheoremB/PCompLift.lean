module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Core

variable {A A' : Type*} [Group A] [Group A'] [Finite A]

theorem glaPPrimeCore_map_of_surjective {p : ℕ} (hp : p.Prime) (f : A →* A')
    (hf : Function.Surjective f) (hker : Nat.Coprime p (Nat.card f.ker)) :
    (GLAPPrimeCore p A).map f = GLAPPrimeCore p A' := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite A' := Finite.of_surjective f hf
  refine le_antisymm ?_ ?_
  · refine le_sSup ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) CFSG.pPrimeCore_coprime_card
  · set R := GLAPPrimeCore p A' with hR
    have hcopR : Nat.Coprime p (Nat.card R) := CFSG.pPrimeCore_coprime_card
    have hnorm : (R.comap f).Normal := Subgroup.Normal.comap inferInstance f
    have hcop : Nat.Coprime p (Nat.card (R.comap f)) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R.comap f)) p hd
      have hgp : (g : A) ^ p = 1 := by
        have := pow_orderOf_eq_one g
        rw [hg] at this
        exact congrArg Subtype.val this
      have hfg : f g ∈ R := g.2
      have hfgp : (⟨f g, hfg⟩ : ↥R) ^ p = 1 := Subtype.ext (by simp [← map_pow, hgp])
      have h1 : orderOf (⟨f g, hfg⟩ : ↥R) ∣ p := orderOf_dvd_of_pow_eq_one hfgp
      have h2 : orderOf (⟨f g, hfg⟩ : ↥R) ∣ Nat.card R := orderOf_dvd_natCard _
      have h3 : orderOf (⟨f g, hfg⟩ : ↥R) = 1 := Nat.eq_one_of_dvd_coprimes hcopR h1 h2
      have h4 : f g = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h3)
      have hgk : (g : A) ∈ f.ker := h4
      have h5 : orderOf (⟨(g : A), hgk⟩ : ↥f.ker) = p := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
      have h6 : p ∣ Nat.card f.ker := h5 ▸ orderOf_dvd_natCard _
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hker h6
    have hle : R.comap f ≤ GLAPPrimeCore p A := le_sSup ⟨hnorm, hcop⟩
    calc R = (R.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf R).symm
      _ ≤ (GLAPPrimeCore p A).map f := Subgroup.map_mono hle

end Core

section Res

variable {G G' : Type*} [Group G] [Group G'] [Finite G]

omit [Finite G] in
theorem coprime_card_ker_subgroupMap {p : ℕ} (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    Nat.Coprime p (Nat.card (ψ.subgroupMap A).ker) := by
  rw [Subgroup.ker_subgroupMap]
  have h1 : (ψ.ker.subgroupOf A).map A.subtype = A ⊓ ψ.ker := by
    rw [← Subgroup.inf_subgroupOf_right ψ.ker A,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : ψ.ker ⊓ A ≤ A)]
    exact inf_comm _ _
  have h2 : Nat.card ((ψ.ker.subgroupOf A).map A.subtype) = Nat.card (ψ.ker.subgroupOf A) :=
    Subgroup.card_map_of_injective A.subtype_injective
  rw [← h2, h1]
  exact hker

theorem glaPPrimeCore_map_subgroupMap {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (GLAPPrimeCore p ↥A).map (ψ.subgroupMap A) = GLAPPrimeCore p ↥(A.map ψ) :=
  glaPPrimeCore_map_of_surjective hp _ (ψ.subgroupMap_surjective A)
    (coprime_card_ker_subgroupMap ψ A hker)

@[expose] noncomputable def lcHom {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (↥A ⧸ GLAPPrimeCore p ↥A) →* (↥(A.map ψ) ⧸ GLAPPrimeCore p ↥(A.map ψ)) :=
  QuotientGroup.map _ _ (ψ.subgroupMap A) (by
    rw [← glaPPrimeCore_map_subgroupMap hp ψ A hker]
    exact Subgroup.le_comap_map _ _)

theorem lcHom_mk {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) (x : ↥A) :
    lcHom hp ψ A hker (QuotientGroup.mk x) = QuotientGroup.mk (ψ.subgroupMap A x) :=
  rfl

theorem lcHom_bijective {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    Function.Bijective (lcHom hp ψ A hker) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (QuotientGroup.mk (ψ.subgroupMap A x) : ↥(A.map ψ) ⧸ _) = 1 := hq
    rw [QuotientGroup.eq_one_iff, ← glaPPrimeCore_map_subgroupMap hp ψ A hker] at h1
    obtain ⟨o, ho, hox⟩ := h1
    have hk : o⁻¹ * x ∈ (ψ.subgroupMap A).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hox, inv_mul_cancel]
    have hkO : (ψ.subgroupMap A).ker ≤ GLAPPrimeCore p ↥A :=
      le_sSup ⟨MonoidHom.normal_ker _, coprime_card_ker_subgroupMap ψ A hker⟩
    have : x = o * (o⁻¹ * x) := by simp
    rw [QuotientGroup.eq_one_iff, this]
    exact Subgroup.mul_mem _ ho (hkO hk)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := ψ.subgroupMap_surjective A y
    exact ⟨QuotientGroup.mk x, rfl⟩

@[expose] noncomputable def lcEquiv {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (↥A ⧸ GLAPPrimeCore p ↥A) ≃* (↥(A.map ψ) ⧸ GLAPPrimeCore p ↥(A.map ψ)) :=
  MulEquiv.ofBijective (lcHom hp ψ A hker) (lcHom_bijective hp ψ A hker)

noncomputable abbrev lcMonoidHom {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (↥A ⧸ GLAPPrimeCore p ↥A) →* (↥(A.map ψ) ⧸ GLAPPrimeCore p ↥(A.map ψ)) :=
  (lcEquiv hp ψ A hker : _ →* _)

noncomputable abbrev lcMonoidHomInv {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    (↥(A.map ψ) ⧸ GLAPPrimeCore p ↥(A.map ψ)) →* (↥A ⧸ GLAPPrimeCore p ↥A) :=
  ((lcEquiv hp ψ A hker).symm : _ →* _)

theorem lcEquiv_barX {p : ℕ} (hp : p.Prime) (ψ : G →* G') (A : Subgroup G)
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) {S : Subgroup G} (hS : S ≤ A) :
    (barX p A S).map (lcMonoidHom hp ψ A hker) = barX p (A.map ψ) (S.map ψ) := by
  ext z
  simp only [barX, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨ψ.subgroupMap A x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hsy⟩ := (Subgroup.mem_subgroupOf).1 hy
    refine ⟨QuotientGroup.mk ⟨s, hS hs⟩, ⟨⟨s, hS hs⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩, ?_⟩
    show QuotientGroup.mk (ψ.subgroupMap A ⟨s, hS hs⟩) = QuotientGroup.mk y
    congr 1
    exact Subtype.ext hsy

end Res

section Comp

variable {G G' : Type*} [Group G] [Group G'] [Finite G]

omit [Finite G] in
theorem isSubnormal_comap_inf (ψ : G →* G') {A : Subgroup G} {J : Subgroup G'}
    (hJ : IsSubnormal J (A.map ψ)) : IsSubnormal (J.comap ψ ⊓ A) A := by
  have h1 := isSubnormal_comap' ψ hJ
  have h2 := isSubnormal_inf h1 A
  rwa [inf_eq_right.2 (Subgroup.le_comap_map ψ A)] at h2

theorem glaPComponent_map {p : ℕ} (hp : p.Prime) (ψ : G →* G') {A K : Subgroup G}
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) (hK : GLAPComponent p A K) :
    GLAPComponent p (A.map ψ) (K.map ψ) := by
  obtain ⟨hKA, hsn, hcomp, hmin⟩ := hK
  have hbar := lcEquiv_barX hp ψ A hker hKA
  refine ⟨Subgroup.map_mono hKA, isSubnormal_map' ψ hsn, ?_, ?_⟩
  · have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (lcEquiv hp ψ A hker)
      (hcomp : IsComponentOf (barX p A K) ⊤)
    have htop : (⊤ : Subgroup (↥A ⧸ GLAPPrimeCore p ↥A)).map (lcMonoidHom hp ψ A hker) = ⊤ :=
      Subgroup.map_top_of_surjective (lcMonoidHom hp ψ A hker) (lcEquiv hp ψ A hker).surjective
    rw [htop] at this
    show IsComponentOf (barX p (A.map ψ) (K.map ψ)) ⊤
    rw [← hbar]
    exact this
  · intro J hJ hJsn heq
    set J' : Subgroup G := J.comap ψ ⊓ K with hJ'
    have hJ'K : J' ≤ K := inf_le_right
    have hJ'sn : IsSubnormal J' A := by
      have h1 := isSubnormal_comap_inf ψ hJsn
      have h3 := isSubnormal_inf h1 K
      rw [inf_assoc, inf_eq_right.2 hKA] at h3
      exact isSubnormal_trans' h3 hsn
    have hmapJ' : J'.map ψ = J := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, ⟨hxJ, -⟩, rfl⟩
        exact hxJ
      · intro y hy
        obtain ⟨k, hk, rfl⟩ := hJ.le hy
        exact ⟨k, ⟨hy, hk⟩, rfl⟩
    have hlt : J' < K := by
      refine lt_of_le_of_ne hJ'K fun h => hJ.ne ?_
      rw [← hmapJ', h]
    refine hmin J' hlt hJ'sn ?_
    show barX p A J' = barX p A K
    have e1 := lcEquiv_barX hp ψ A hker (hJ'K.trans hKA)
    rw [hmapJ'] at e1
    have : (barX p A J').map (lcMonoidHom hp ψ A hker) =
        (barX p A K).map (lcMonoidHom hp ψ A hker) := by
      rw [e1, hbar]
      exact heq
    exact Subgroup.map_injective (lcEquiv hp ψ A hker).injective this

theorem exists_glaPComponent_map_eq {p : ℕ} (hp : p.Prime) (ψ : G →* G') {A : Subgroup G}
    (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) {K' : Subgroup G'}
    (hK' : GLAPComponent p (A.map ψ) K') :
    ∃ K : Subgroup G, GLAPComponent p A K ∧ K.map ψ = K' := by
  obtain ⟨hK'A, hsn', hcomp', hmin'⟩ := hK'
  set 𝒮 : Set (Subgroup G) := {S | S ≤ A ∧ IsSubnormal S A ∧ S.map ψ ≤ K' ∧
    barX p (A.map ψ) (S.map ψ) = barX p (A.map ψ) K'} with h𝒮
  have hS₀ : K'.comap ψ ⊓ A ∈ 𝒮 := by
    have hmap : (K'.comap ψ ⊓ A).map ψ = K' := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨a, ha, rfl⟩ := hK'A hy
        exact ⟨a, ⟨hy, ha⟩, rfl⟩
    exact ⟨inf_le_right, isSubnormal_comap_inf ψ hsn', hmap.le, by rw [hmap]⟩
  obtain ⟨S, ⟨hSA, hSsn, hSK', hSbar⟩, hSmin⟩ :=
    (wellFounded_lt (α := Subgroup G)).has_min 𝒮 ⟨_, hS₀⟩
  have hSmap : S.map ψ = K' := by
    by_contra hne
    exact hmin' (S.map ψ) (lt_of_le_of_ne hSK' hne) (isSubnormal_map' ψ hSsn) hSbar
  refine ⟨S, ⟨hSA, hSsn, ?_, ?_⟩, hSmap⟩
  · have e := lcEquiv_barX hp ψ A hker hSA
    rw [hSmap] at e
    have hc : IsComponentOf (barX p (A.map ψ) K') ⊤ := hcomp'
    have h1 : IsComponentOf ((barX p A S).map (lcMonoidHom hp ψ A hker)) ⊤ := by
      rw [e]
      exact hc
    have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map
      (lcEquiv hp ψ A hker).symm h1
    have htop : (⊤ : Subgroup (↥(A.map ψ) ⧸ GLAPPrimeCore p ↥(A.map ψ))).map
        (lcMonoidHomInv hp ψ A hker) = ⊤ :=
      Subgroup.map_top_of_surjective (lcMonoidHomInv hp ψ A hker)
        (lcEquiv hp ψ A hker).symm.surjective
    have h2 : ((barX p A S).map (lcMonoidHom hp ψ A hker)).map (lcMonoidHomInv hp ψ A hker) =
        barX p A S := by
      rw [Subgroup.map_map]
      have : (lcMonoidHomInv hp ψ A hker).comp (lcMonoidHom hp ψ A hker) = MonoidHom.id _ := by
        ext x
        simp
      rw [this, Subgroup.map_id]
    rw [htop, h2] at this
    exact this
  · intro J hJ hJsn heq
    refine hSmin J ⟨hJ.le.trans hSA, hJsn, (Subgroup.map_mono hJ.le).trans hSmap.le, ?_⟩ hJ
    have e1 := lcEquiv_barX hp ψ A hker (hJ.le.trans hSA)
    have e2 := lcEquiv_barX hp ψ A hker hSA
    rw [← e1, show barX p A J = barX p A S from heq, e2, hSbar]

end Comp

end CFSG.LocalAnalysis.GLTheoremB
