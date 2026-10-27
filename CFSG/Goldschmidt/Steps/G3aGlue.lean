module

public import CFSG.Goldschmidt.Steps.G3aComp

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace G3a

section Sylow

variable {G : Type} [Group G]

theorem fusionIsSylowIn_of_sylow {S X : Subgroup G} (hSX : S ≤ X) (P : Sylow 2 X)
    (hP : (P : Subgroup X) = S.subgroupOf X) : fusionIsSylowIn 2 S X := by
  have hS : IsPGroup 2 S := by
    have h1 := P.isPGroup'.map X.subtype
    rwa [hP, Subgroup.map_subgroupOf_eq_of_le hSX] at h1
  refine ⟨hSX, hS, fun R hRX hR hSR => ?_⟩
  have h1 := P.is_maximal' (Q := R.subgroupOf X) hR.comap_subtype (by
    rw [hP]
    exact fun x hx => hSR hx)
  rw [hP] at h1
  have h2 := congrArg (Subgroup.map X.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hRX, Subgroup.map_subgroupOf_eq_of_le hSX] at h2

variable [Finite G]

theorem fusionIsSylowIn_inf {T X M : Subgroup G} (hTX : fusionIsSylowIn 2 T X) (hMX : M ≤ X)
    (hM : (M.subgroupOf X).IsSubnormal) : fusionIsSylowIn 2 (T ⊓ M) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨TX, hTX'⟩ := exists_sylow_of_fusionIsSylowIn hTX
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal TX hM
  let e : M.subgroupOf X ≃* M := Subgroup.subgroupOfEquivOfLe hMX
  have he : Function.Surjective e.toMonoidHom := e.surjective
  refine fusionIsSylowIn_of_sylow inf_le_right (P.mapSurjective he) ?_
  rw [Sylow.coe_mapSurjective]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : (y : X) ∈ (P : Subgroup (M.subgroupOf X)).map (M.subgroupOf X).subtype :=
      ⟨y, hy, rfl⟩
    rw [hP, hTX'] at h1
    exact ⟨h1.1, (e.toMonoidHom y).2⟩
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have h1 : ((e.symm x : M.subgroupOf X) : X) ∈ (TX : Subgroup X) ⊓ M.subgroupOf X := by
      rw [hTX']
      exact ⟨hx.1, (e.symm x).2⟩
    rw [← hP] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    rwa [show z = e.symm x from Subtype.ext hzx] at hz

end Sylow

section Transport

@[expose] noncomputable def quotientEquivRange {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (N : Subgroup X) [N.Normal] (h : N = φ.ker) : X ⧸ N ≃* φ.range :=
  (QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange φ)

theorem quotientEquivRange_mk {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    (N : Subgroup X) [N.Normal] (h : N = φ.ker) (x : X) :
    ((quotientEquivRange φ N h (QuotientGroup.mk' N x) : φ.range) : Y) = φ x := rfl

noncomputable def centerQuotientEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)

theorem isGoldTypeI_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsGoldTypeI X) : IsGoldTypeI Y := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨(centerQuotientEquiv e).symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨(centerQuotientEquiv e).symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨(centerQuotientEquiv e).symm.trans f⟩⟩)

theorem isGoldTypeII_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : IsGoldTypeII X) : IsGoldTypeII Y := by
  obtain ⟨hodd, hL2 | hJR⟩ := h
  · refine ⟨?_, Or.inl ?_⟩
    · rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
      exact hodd
    · obtain ⟨p, f, hp, hpo, hf, h5, h8, ⟨g⟩⟩ := hL2
      exact ⟨p, f, hp, hpo, hf, h5, h8, ⟨(centerQuotientEquiv e).symm.trans g⟩⟩
  · refine ⟨?_, Or.inr ?_⟩
    · rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
      exact hodd
    · exact CFSG.Walter.IsTypeJR.of_mulEquiv (centerQuotientEquiv e) hJR

theorem omega1_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (hf : Function.Injective f)
    (T : Subgroup X) : (Omega1 T).map f = Omega1 (T.map f) := by
  unfold Omega1
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨t, ⟨ht, ht2⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, by rw [← map_pow, ht2, map_one]⟩
  · rintro ⟨⟨t, ht, rfl⟩, ht2⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    apply hf
    rw [map_pow, ht2, map_one]

theorem open_isSubnormal_comap {Y Z : Type*} [Group Y] [Group Z] (f : Z →* Y)
    {M N : Subgroup Y} (h : CFSG.Open.IsSubnormal M N) :
    CFSG.Open.IsSubnormal (M.comap f) (N.comap f) :=
  h.comap f

theorem isComponentOf_subgroupOf {X : Type*} [Group X] {L R : Subgroup X}
    (h : IsComponentOf L R) : IsComponentOf (L.subgroupOf R) ⊤ := by
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩
  have := open_isSubnormal_comap R.subtype h.2.1
  exact (Subgroup.subgroupOf_self (H := R)) ▸ this

end Transport

section Conf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalClosureIn_le (H A : Subgroup G) : normalClosureIn H A ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalClosureIn {H A : Subgroup G} (hAH : A ≤ H) : A ≤ normalClosureIn H A :=
  fun a ha => ⟨⟨a, hAH ha⟩, Subgroup.subset_normalClosure ha, rfl⟩

omit [Finite G] in
theorem normalClosureIn_normal (H A : Subgroup G) :
    ((normalClosureIn H A).subgroupOf H).Normal := by
  have h : (normalClosureIn H A).subgroupOf H =
      Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h]
  infer_instance

theorem normalClosure_eq_top {H A T : Subgroup G} (hAH : A ≤ H) (hT : fusionIsSylowIn 2 T H)
    (hAT : A ≤ T) (hcl : IsStronglyClosedIn A T H) :
    Subgroup.normalClosure ((A.subgroupOf (normalClosureIn H A) : Subgroup _) :
      Set (normalClosureIn H A)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := normalClosureIn H A with hK
  set N : Subgroup H := Subgroup.normalClosure ((A.subgroupOf H : Subgroup H) : Set H) with hN
  have hKN : K.subgroupOf H = N := Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  have hAK : A ≤ K := le_normalClosureIn hAH
  obtain ⟨TH, hTH⟩ := exists_sylow_of_fusionIsSylowIn hT
  obtain ⟨PN, hPN⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal TH
    (Subgroup.Normal.isSubnormal (inferInstance : N.Normal))
  have hfr := Sylow.normalizer_sup_eq_top PN
  set M : Subgroup G := (Subgroup.normalClosure
    ((A.subgroupOf K : Subgroup K) : Set K)).map K.subtype with hM
  have hconj : ∀ h : H, ∀ a ∈ A, (h : G) * a * (h : G)⁻¹ ∈ M := by
    intro h a ha
    have hh : h ∈ N ⊔ Subgroup.normalizer
        (((PN : Subgroup N).map N.subtype : Subgroup H) : Set H) := by
      rw [sup_comm, hfr]
      exact Subgroup.mem_top h
    obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
    have haN : (⟨a, hAH ha⟩ : H) ∈ (PN : Subgroup N).map N.subtype := by
      rw [hPN, hTH]
      refine ⟨hAT ha, ?_⟩
      rw [← hKN]
      exact hAK ha
    have hna := (Subgroup.mem_normalizer_iff.mp hn _).mp haN
    rw [hPN, hTH] at hna
    have hnaT : (n : G) * a * (n : G)⁻¹ ∈ T := hna.1
    have hnaA : (n : G) * a * (n : G)⁻¹ ∈ A := by
      have := hcl a ha (n : G)⁻¹ (H.inv_mem n.2) (by rwa [inv_inv])
      rwa [inv_inv] at this
    have hkK : (k : G) ∈ K := by
      rw [← hKN] at hk
      exact hk
    have hnaK : (n : G) * a * (n : G)⁻¹ ∈ K := hAK hnaA
    refine ⟨⟨(k : G), hkK⟩ * ⟨_, hnaK⟩ * ⟨(k : G), hkK⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance _
        (Subgroup.subset_normalClosure (show (⟨_, hnaK⟩ : K) ∈ A.subgroupOf K from hnaA)) _
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hKM : K ≤ M := by
    rw [hK]
    unfold normalClosureIn
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    exact hconj c a ha
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨y, hy, hyx⟩ := hKM hx
  rwa [show y = ⟨x, hx⟩ from Subtype.ext hyx] at hy

theorem sconf_of_isSStarIn {H A : Subgroup G} (hS : IsSStarIn H A) :
    ∃ T : Subgroup G, fusionIsSylowIn 2 T H ∧ A ≤ T ∧ IsStronglyClosedIn A T H ∧
      ∃ P : Sylow 2 (normalClosureIn H A ⧸ goldschmidtOddCore (normalClosureIn H A)),
        (P : Subgroup _) = barOf (normalClosureIn H A) T ∧
        SConf P (barOf (normalClosureIn H A) A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAH, hAc, T, hT, hAT, hcl, hK⟩ := hS
  obtain ⟨hgen, hcen, hbar, htypes⟩ := hK
  set K := normalClosureIn H A with hKdef
  have hKH : K ≤ H := normalClosureIn_le H A
  have hKn := normalClosureIn_normal H A
  have hTK := fusionIsSylowIn_inf hT hKH hKn.isSubnormal
  obtain ⟨PK, hPK⟩ := exists_sylow_of_fusionIsSylowIn hTK
  have hPK' : (PK : Subgroup K) = T.subgroupOf K := by
    rw [hPK]
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hA'P : A.subgroupOf K ≤ PK := by
    rw [hPK']
    exact fun x hx => hAT hx
  have hcl' : fusionStronglyClosed ((A.subgroupOf K : Subgroup K) : Set K) (PK : Subgroup K) := by
    intro a ha g hg
    have hg' : g⁻¹ * a * g ∈ T.subgroupOf K := by rw [← hPK']; exact hg
    exact hcl a ha g (hKH g.2) hg'
  obtain ⟨P, hP, hclP⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PK (A.subgroupOf K)
    (goldschmidtOddCore K) hA'P hcl'
  have hPbar : (P : Subgroup _) = barOf K T := by rw [hP, hPK']; rfl
  refine ⟨T, hT, hAT, hcl, P, hPbar,
    { le := by rw [hPbar]; exact Subgroup.map_mono (fun x hx => hAT hx)
      comm := ?_
      closed := hclP
      top := normalClosure_map_eq_top (normalClosure_eq_top hAH hT hAT hcl) _
        (QuotientGroup.mk'_surjective _)
      odd := goldschmidtOddCore_quotient_eq_bot K
      gen := hgen
      central := hcen
      bar := by rw [hPbar]; exact hbar
      types := htypes }⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have h := congrArg Subtype.val (hAc.is_comm.comm ⟨(x : G), hx⟩ ⟨(y : G), hy⟩)
  exact h

end Conf

end G3a

end CFSG.Goldschmidt
