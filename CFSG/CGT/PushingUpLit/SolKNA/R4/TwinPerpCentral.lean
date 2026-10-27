module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenL62

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem comm_of_isCyclic {R : Subgroup G} [IsCyclic ↥R] :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  letI := IsCyclic.commGroup (α := ↥R)
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥R) ⟨b, hb⟩)

private theorem comm_of_zpowers {z : G} {R : Subgroup G} (h : R = Subgroup.zpowers z) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  rw [h] at ha hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((Commute.refl z).zpow_zpow m n).eq

private theorem false_of_comm {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K) (hc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) : False := by
  obtain ⟨-, P, hP, hPnc⟩ := hΩ.omega1 K hK
  obtain ⟨g, -, hgP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR hP
  apply hPnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hmem : ∀ c ∈ P, g⁻¹ * c * g ∈ R := fun c hcP => by
    rw [← hgP] at hcP
    exact mem_conjSub_iff.mp hcP
  have hab := hc _ (hmem a.1 a.2) _ (hmem b.1 b.2)
  show a.1 * b.1 = b.1 * a.1
  calc a.1 * b.1 = g * ((g⁻¹ * a.1 * g) * (g⁻¹ * b.1 * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b.1 * g) * (g⁻¹ * a.1 * g)) * g⁻¹ := by rw [hab]
    _ = b.1 * a.1 := by group

private theorem exists_normalizes_not_mem {T V : Subgroup G} (hV : IsPGroup 2 V)
    (hTV : T ≤ V) (hne : T ≠ V) : ∃ x ∈ V, (∀ t ∈ T, x⁻¹ * t * x ∈ T) ∧ x ∉ T := by
  haveI : Group.IsNilpotent ↥V := hV.isNilpotent
  have hU : T.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hTV fun v hv => ?_
    have hmem : (⟨v, hv⟩ : ↥V) ∈ T.subgroupOf V := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨y, hyN, hyU⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := ↥V) _ hU)
  refine ⟨y, y.2, fun t ht => ?_, fun hy => hyU (Subgroup.mem_subgroupOf.mpr hy)⟩
  have hsV : (y : G)⁻¹ * t * (y : G) ∈ V := V.mul_mem (V.mul_mem (V.inv_mem y.2) (hTV ht)) y.2
  have hconj : y * ⟨(y : G)⁻¹ * t * (y : G), hsV⟩ * y⁻¹ ∈ T.subgroupOf V := by
    have heq : y * ⟨(y : G)⁻¹ * t * (y : G), hsV⟩ * y⁻¹ = (⟨t, hTV ht⟩ : ↥V) :=
      Subtype.ext (by simp [mul_assoc])
    rw [heq]
    exact Subgroup.mem_subgroupOf.mpr ht
  have hs := (Subgroup.mem_normalizer_iff.mp hyN ⟨(y : G)⁻¹ * t * (y : G), hsV⟩).mpr hconj
  exact Subgroup.mem_subgroupOf.mp hs

private theorem mem_of_isSylow2In_of_isUniqueInvolution {K R : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hR : IsSylow2In R K) : z ∈ R := by
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  obtain ⟨W, hW, hzW⟩ := IsSylow2In.exists_ge hz2 (Subgroup.zpowers_le.mpr hz.mem)
  obtain ⟨g, hgK, hgW⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR hW
  have hzgR : z ∈ conjSub g R := by
    rw [hgW]
    exact hzW (Subgroup.mem_zpowers z)
  rw [mem_conjSub_iff] at hzgR
  have hy : g⁻¹ * z * g ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hgK) hz.mem) hgK
  have hy2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz.sq]; group
  have hy1 : g⁻¹ * z * g ≠ 1 := by
    intro h1
    apply hz.ne_one
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hyz : g⁻¹ * z * g = z := (hz.unique _ hy hy2).resolve_left hy1
  rw [hyz] at hzgR
  exact hzgR

theorem conj_eq_of_le_centralizer {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hnbr : ∀ J ∈ Ω, ∀ L ∈ omegaNbr Ω J, L ∈ twinSet Ω J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : IsSylow2In R K) {g : G}
    (hgR : R ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) : g * z * g⁻¹ = z := by
  by_contra hne
  have hzR : z ∈ R := mem_of_isSylow2In_of_isUniqueInvolution hz hR
  have hRsyl : IsSylow2In R (K ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G)) :=
    ⟨le_inf hR.1 hgR, hR.2.1, fun V'' hV''le hV''2 hRV'' =>
      hR.2.2 V'' (hV''le.trans inf_le_left) hV''2 hRV''⟩
  have hK' : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hpair : Sec6Gen.Pair Ω (conjSub g K) K (g * z * g⁻¹) z :=
    ⟨hK', hK, hz.conj g, hz, hne⟩
  rcases Sec6Gen.Pair.six_two hΩ hpair hRsyl hzR with h1 | h2 | h3 | h4
  · exact false_of_comm hΩ hK hR (comm_of_zpowers h1.1)
  · exact false_of_comm hΩ hK hR (comm_of_zpowers h2.1)
  · obtain ⟨-, -, -, hcyc, -⟩ := h3.1
    haveI := hcyc
    exact false_of_comm hΩ hK hR comm_of_isCyclic
  · obtain ⟨hRΩ, hcomm4⟩ := h4
    have hoc : oddCoreOf (conjSub g K) ≤ conjSub g K := by
      unfold oddCoreOf
      exact Subgroup.map_subtype_le _
    have hcR : ∀ r ∈ R, ∀ k ∈ conjSub g K, r * k * r⁻¹ ∈ conjSub g K := by
      intro r hr k hk
      have hc : ⁅r, k⁆ ∈ conjSub g K :=
        hoc (hcomm4 (Subgroup.commutator_mem_commutator hr hk))
      rw [commutatorElement_def] at hc
      have heq : r * k * r⁻¹ = (r * k * r⁻¹ * k⁻¹) * k := by group
      rw [heq]
      exact (conjSub g K).mul_mem hc hk
    have hRN : R ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact hcR r hr h
      · intro hh
        have h2 := hcR r⁻¹ (R.inv_mem hr) _ hh
        have h3 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
        rw [h3] at h2
        exact h2
    have hKK : K ≠ conjSub g K := by
      intro heq
      apply hne
      have h' : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
      rw [← heq] at h'
      exact (hz.eq h').symm
    have hKnbr : K ∈ omegaNbr Ω (conjSub g K) := ⟨hK, hKK, R, hRΩ, hR.1, hRN⟩
    obtain ⟨-, w, hw', hw⟩ := hnbr (conjSub g K) hK' K hKnbr
    exact hne (((hz.conj g).eq hw').trans (hz.eq hw).symm)

theorem isSylow2In_top_of_nbr_twin {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hnbr : ∀ J ∈ Ω, ∀ L ∈ omegaNbr Ω J, L ∈ twinSet Ω J)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : IsSylow2In R K)
    {T : Subgroup G} (hT : IsSylow2In T (Subgroup.centralizer ({z} : Set G))) (hRT : R ≤ T) :
    IsSylow2In T ⊤ := by
  have hzZ : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hT.1 ht)
  refine ⟨le_top, hT.2.1, fun V' _ hV'2 hTV' => ?_⟩
  by_contra hne
  obtain ⟨x, hxV', hxN, hxT⟩ := exists_normalizes_not_mem hV'2 hTV' (fun h => hne h.symm)
  have hxz : x * z ≠ z * x := by
    intro hcomm
    have hxC : x ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hVC : T ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le hT.1 (Subgroup.zpowers_le.mpr hxC)
    have hV2 : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers x) :=
      hV'2.to_le (sup_le hTV' (Subgroup.zpowers_le.mpr hxV'))
    have heq : T ⊔ Subgroup.zpowers x = T := hT.2.2 _ hVC hV2 le_sup_left
    have hxT' : x ∈ T ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [heq] at hxT'
    exact hxT hxT'
  have hz'T : ∀ t ∈ T, t * (x * z * x⁻¹) = (x * z * x⁻¹) * t := by
    intro t ht
    have hc : (x⁻¹ * t * x) * z = z * (x⁻¹ * t * x) := hzZ _ (hxN t ht)
    calc t * (x * z * x⁻¹) = x * ((x⁻¹ * t * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc]
      _ = (x * z * x⁻¹) * t := by group
  have hz'ne : x * z * x⁻¹ ≠ z := fun h => hxz (mul_inv_eq_iff_eq_mul.mp h)
  have hRC : R ≤ Subgroup.centralizer ({x * z * x⁻¹} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz'T r (hRT hr))
  exact hz'ne (conj_eq_of_le_centralizer hΩ hnbr hK hz hR hRC)

theorem nbr_twin_of_kPerp_eq (K₀ : Subgroup G)
    (h : KPerp (CoreAssembly.conjClass K₀) K₀ = twinSet (CoreAssembly.conjClass K₀) K₀) :
    ∀ J ∈ CoreAssembly.conjClass K₀, ∀ L ∈ omegaNbr (CoreAssembly.conjClass K₀) J,
      L ∈ twinSet (CoreAssembly.conjClass K₀) J := by
  intro J hJ L hL
  obtain ⟨g, hg⟩ := hJ
  have hJg : J = conjSub g K₀ := hg.symm
  subst hJg
  have hΩ := conjInvariant_conjClass K₀
  have hL0 : conjSub g⁻¹ L ∈ omegaNbr (CoreAssembly.conjClass K₀) K₀ := by
    have := omegaNbr_conj hΩ hL g⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hmem : conjSub g⁻¹ L ∈ KPerp (CoreAssembly.conjClass K₀) K₀ :=
    Set.mem_insert_of_mem _ hL0
  rw [h] at hmem
  have := twinSet_conj hΩ hmem g
  rwa [conjSub_conjSub_inv] at this

end CFSG.CGT.PushingUpLit.SolKNA.R4
