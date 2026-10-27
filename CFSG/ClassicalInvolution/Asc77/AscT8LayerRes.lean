module

public import CFSG.ClassicalInvolution.Asc77.AscT8Min
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped commutatorElement

namespace T8

section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def cenZ (x : G) : Subgroup G :=
  Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_cenZ_iff {x g : G} : g ∈ cenZ x ↔ g * x = x * g := by
  unfold cenZ
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h x (Subgroup.mem_zpowers x)).symm
  · intro h y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute x g from h.symm) m).symm).eq.symm

omit [Finite G] in
theorem cenZ_eq_centralizer (x : G) : cenZ x = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [mem_cenZ_iff, Subgroup.mem_centralizer_singleton_iff]

@[expose] def XMem (Ω : Set (Subgroup G)) (x : G) (K : Subgroup G) : Prop :=
  K ∈ Ω ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
    ∃ R : Subgroup G, IsSylow2In R K ∧ ∀ r ∈ R, r * x = x * r

@[expose] def layerRes (x : G) (K : Subgroup G) : Subgroup G :=
  perfectResidualOf (K ⊓ cenZ x)

@[expose] def layerSet (Ω : Set (Subgroup G)) (x : G) : Set (Subgroup G) :=
  {L | ∃ K, XMem Ω x K ∧ L = layerRes x K}

omit [Finite G] in
theorem exists_orderOf_eq_two_pow {x : G} (hx : x * x = 1) : ∃ n : ℕ, orderOf x = 2 ^ n := by
  have h : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

omit [Finite G] in
theorem XMem.conj (hΩ : HypOmegaMod p f Ω) {x : G} {K : Subgroup G} (h : XMem Ω x K) {n : G}
    (hn : n ∈ cenZ x) : XMem Ω x (conjSub n K) := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have hnx : n * x = x * n := mem_cenZ_iff.mp hn
  have hnx' : n⁻¹ * x = x * n⁻¹ := by
    calc n⁻¹ * x = n⁻¹ * (x * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * x) * n⁻¹ := by rw [hnx]
      _ = x * n⁻¹ := by group
  refine ⟨hΩ.conjInvariant n K hK, ?_, conjSub n R, hR.conj n, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
    rw [← conjSub_mul, ← hnx, conjSub_mul, hN]
  · intro r hr
    rw [mem_conjSub_iff] at hr
    have h1 := hRx _ hr
    calc r * x = n * (n⁻¹ * r * n) * (n⁻¹ * x) := by group
      _ = n * (n⁻¹ * r * n) * (x * n⁻¹) := by rw [hnx']
      _ = n * ((n⁻¹ * r * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * r * n)) * n⁻¹ := by rw [h1]
      _ = (n * x) * (n⁻¹ * r * n) * n⁻¹ := by group
      _ = (x * n) * (n⁻¹ * r * n) * n⁻¹ := by rw [hnx]
      _ = x * r := by group

omit [Finite G] in
theorem conjSub_cenZ {x n : G} (hn : n ∈ cenZ x) : conjSub n (cenZ x) = cenZ x :=
  conjSub_eq_self_of_mem hn

theorem layerRes_conj {x : G} (K : Subgroup G) {n : G} (hn : n ∈ cenZ x) :
    conjSub n (layerRes x K) = layerRes x (conjSub n K) := by
  unfold layerRes
  rw [← perfectResidualOf_conjSub, conjSub_inf, conjSub_cenZ hn]

theorem layerSet_conj (hΩ : HypOmegaMod p f Ω) {x : G} {L : Subgroup G} (hL : L ∈ layerSet Ω x)
    {n : G} (hn : n ∈ cenZ x) : conjSub n L ∈ layerSet Ω x := by
  obtain ⟨K, hK, rfl⟩ := hL
  exact ⟨conjSub n K, hK.conj hΩ hn, layerRes_conj K hn⟩

theorem XMem.zpowers_le_trivialOnQuot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) :
    Subgroup.zpowers x ≤ trivialOnQuot K := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have h3 := lemma_3_3_member_element hp hq hΩ hK hR (exists_orderOf_eq_two_pow hx) hN hRx
  exact Subgroup.zpowers_le.mpr ⟨hN, fun k hk => h3 k hk⟩

theorem XMem.axisResidual (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {z : G} (hz : IsClassicalMember p f K z) :
    AxisResidual K (Subgroup.zpowers x) (layerRes x K) z := by
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hz.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  have hzc : ∀ y ∈ K, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hz.subnormal hy)
  exact axisResidual_perfectResidual hz.perfect hz.mem hz2 hzc hz.subnormal
    (isPGroup_zpowers_of_sq hx) (h.zpowers_le_trivialOnQuot hp hq hΩ hx)

theorem XMem.isSectionMember (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {z : G} (hz : IsClassicalMember p f K z) :
    IsSectionMember p f (cenZ x) (layerRes x K) z :=
  AxisResidual.isSectionMember hz (h.axisResidual hp hq hΩ hx hz)
    (finite_perfectResidualOf_isPerfect _)

omit [Finite G] in
theorem le_normalizer_of_conj_mem {J K : Subgroup G}
    (hf : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K) : J ≤ Subgroup.normalizer (K : Set G) := by
  intro j hj
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨hf j hj h, fun hh => ?_⟩
  have h2 := hf j⁻¹ (J.inv_mem hj) _ hh
  have e : j⁻¹ * (j * h * j⁻¹) * j⁻¹⁻¹ = h := by group
  rwa [e] at h2

omit [Finite G] in
theorem mem_normalizer_layerRes {x j : G} {K : Subgroup G}
    (hjK : j ∈ Subgroup.normalizer (K : Set G)) (hjx : j ∈ cenZ x) :
    j ∈ Subgroup.normalizer (layerRes x K : Set G) := by
  have h1 : j ∈ Subgroup.normalizer ((K ⊓ cenZ x : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq] at hjK ⊢
    rw [conjSub_inf, hjK, conjSub_cenZ hjx]
  exact perfectResidualOf_normalizer_contains _ h1

omit [Finite G] in
theorem padicValNat_two_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat 2 a ≤ padicValNat 2 b :=
  (padicValNat_dvd_iff_le hb).1 ((pow_padicValNat_dvd (p := 2) (n := a)).trans h)

theorem layerRes_omega4 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hne : layerRes x K ≠ layerRes x J) :
    padicValNat 2 (Nat.card ↥(layerRes x K ⊓ layerRes x J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(layerRes x K ⊓ layerRes x J)) = 1 →
        ⁅layerRes x K, layerRes x J⁆ ≤ oddCoreOf (layerRes x K) ⊓ oddCoreOf (layerRes x J)) := by
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK.1
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ.1
  have hRK := hK.axisResidual hp hq hΩ hx hzK
  have hRJ := hJ.axisResidual hp hq hΩ hx hzJ
  have hLK : layerRes x K ≤ K ⊓ cenZ x := Subgroup.map_subtype_le _
  have hLJ : layerRes x J ≤ J ⊓ cenZ x := Subgroup.map_subtype_le _
  obtain ⟨h1, h2⟩ := hΩ.omega4 K hK.1 J hJ.1 hKJ
  have hdvd : Nat.card ↥(layerRes x K ⊓ layerRes x J) ∣ Nat.card ↥(K ⊓ J) :=
    Subgroup.card_dvd_of_le (inf_le_inf (hLK.trans inf_le_left) (hLJ.trans inf_le_left))
  have hle := padicValNat_two_le_of_dvd Nat.card_pos.ne' hdvd
  refine ⟨hle.trans h1, fun h => ?_⟩
  have hcomm := h2 (le_antisymm h1 (h ▸ hle))
  have hcK : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
    intro j hj k hk
    have h3 : ⁅j, k⁆ ∈ ⁅K, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hj hk
    have h4 : ⁅j, k⁆ * k = j * k * j⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← h4]
    exact K.mul_mem (oddCoreOf_le_self K (hcomm h3).1) hk
  have hcJ : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have h3 : ⁅k, j⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator hk hj
    have h4 : ⁅k, j⁆ * j = k * j * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← h4]
    exact J.mul_mem (oddCoreOf_le_self J (hcomm h3).2) hj
  have hJNK := le_normalizer_of_conj_mem hcK
  have hKNJ := le_normalizer_of_conj_mem hcJ
  have hLJN : ∀ b ∈ layerRes x J, b ∈ Subgroup.normalizer (layerRes x K : Set G) := fun b hb =>
    mem_normalizer_layerRes (hJNK (hLJ hb).1) (hLJ hb).2
  have hLKN : ∀ a ∈ layerRes x K, a ∈ Subgroup.normalizer (layerRes x J : Set G) := fun a ha =>
    mem_normalizer_layerRes (hKNJ (hLK ha).1) (hLK ha).2
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have h5 : ⁅a, b⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator (hLK ha).1 (hLJ hb).1
  have h6 : ⁅a, b⁆ ∈ layerRes x K := by
    have h7 : b * a⁻¹ * b⁻¹ ∈ layerRes x K :=
      (Subgroup.mem_normalizer_iff.1 (hLJN b hb) a⁻¹).1 ((layerRes x K).inv_mem ha)
    have h8 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h8]
    exact (layerRes x K).mul_mem ha h7
  have h9 : ⁅a, b⁆ ∈ layerRes x J := by
    have h7 : a * b * a⁻¹ ∈ layerRes x J :=
      (Subgroup.mem_normalizer_iff.1 (hLKN a ha) b).1 hb
    have h8 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
      simp only [commutatorElement_def]
    rw [h8]
    exact (layerRes x J).mul_mem h7 ((layerRes x J).inv_mem hb)
  have hoK : oddCoreOf (layerRes x K) = layerRes x K ⊓ oddCoreOf K := hRK.oddCoreIn_eq
  have hoJ : oddCoreOf (layerRes x J) = layerRes x J ⊓ oddCoreOf J := hRJ.oddCoreIn_eq
  rw [hoK, hoJ]
  exact ⟨⟨h6, (hcomm h5).1⟩, ⟨h9, (hcomm h5).2⟩⟩

theorem XMem.isUniqueInvolution_layerRes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {z : G}
    (hz : IsUniqueInvolution K z) : IsUniqueInvolution (layerRes x K) z := by
  obtain ⟨z', hz'⟩ := hΩ.classical K h.1
  have hz'U := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz'
  have hzz' : z = z' := hz.eq hz'U
  subst hzz'
  have hLK : layerRes x K ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  exact ⟨(h.axisResidual hp hq hΩ hx hz').mem, hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (hLK hy) hy2⟩

theorem XMem.isUniqueInvolution_of_layerRes (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {x : G} (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {z : G}
    (hz : IsUniqueInvolution (layerRes x K) z) : IsUniqueInvolution K z := by
  obtain ⟨z', hz'⟩ := hΩ.classical K h.1
  have hz'U := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz'
  have hz'L := h.isUniqueInvolution_layerRes hp hq hΩ hx hz'U
  have hzz' : z' = z := hz'L.eq hz
  rw [← hzz']
  exact hz'U

theorem layerRes_omega5 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hne : layerRes x K ≠ layerRes x J) {z : G} (hz : IsUniqueInvolution (layerRes x K) z)
    {v : G} (hv : v ∈ layerRes x J) (hnc : ¬ ∀ w ∈ layerRes x J, v * w = w * v)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (layerRes x K : Set G) := by
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  have hLJ : layerRes x J ≤ J ⊓ cenZ x := Subgroup.map_subtype_le _
  have hzK : IsUniqueInvolution K z := hK.isUniqueInvolution_of_layerRes hp hq hΩ hx hz
  have hnc' : ¬ ∀ w ∈ J, v * w = w * v := fun h =>
    hnc fun w hw => h w (hLJ hw).1
  have hvK : v ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK.1 J hJ.1 hKJ z hzK v (hLJ hv).1 hnc' hv2 hvz
  exact mem_normalizer_layerRes hvK (hLJ hv).2

theorem layerRes_twin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J) {z : G}
    (hzK : IsUniqueInvolution (layerRes x K) z) (hzJ : IsUniqueInvolution (layerRes x J) z) :
    J ∈ twinSet Ω K :=
  ⟨hJ.1, z, hK.isUniqueInvolution_of_layerRes hp hq hΩ hx hzK,
    hJ.isUniqueInvolution_of_layerRes hp hq hΩ hx hzJ⟩

end Layer

section SylowCover

theorem isSylow2In_top_of_cover {H : Type} [Group H] [Finite H] {N L T : Subgroup H} [N.Normal]
    (hN : Odd (Nat.card N)) (hcov : ∀ h : H, ∃ i ∈ L, ∃ n ∈ N, h = i * n) (hT : IsSylow2In T L) :
    IsSylow2In T ⊤ := by
  have hsup : L ⊔ N = ⊤ := eq_top_iff.2 fun h _ => by
    obtain ⟨i, hi, n, hn, rfl⟩ := hcov h
    exact Subgroup.mul_mem_sup hi hn
  have h1 : N.relIndex (L ⊔ N) = N.relIndex L := Subgroup.relIndex_sup_right L N
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.index_mul_card (H := N)
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := L)
  have hodd1 : Odd (Nat.card ↥(N ⊓ L)) := hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hmul : Nat.card H * Nat.card ↥(N ⊓ L) = Nat.card N * Nat.card L := by
    rw [← h2, ← h3, h1]
    ring
  have hfac : (Nat.card H).factorization 2 = (Nat.card L).factorization 2 := by
    have h0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have h0' : Nat.card ↥(N ⊓ L) ≠ 0 := Nat.card_pos.ne'
    have h0N : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have h0L : Nat.card L ≠ 0 := Nat.card_pos.ne'
    have hz1 : (Nat.card ↥(N ⊓ L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd1)
        (even_iff_two_dvd.mpr h))
    have hz2 : (Nat.card N).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hN)
        (even_iff_two_dvd.mpr h))
    have := congrArg (fun m => m.factorization 2) hmul
    simp only [Nat.factorization_mul h0 h0', Nat.factorization_mul h0N h0L, Finsupp.add_apply,
      hz1, hz2, zero_add, add_zero] at this
    exact this
  refine ⟨le_top, hT.2.1, fun V _ hV2 hle => ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  have hdvd : Nat.card V ∣ Nat.card H := by
    simpa [Subgroup.card_top] using Subgroup.card_dvd_of_le (le_top : V ≤ ⊤)
  have hle2 : k ≤ (Nat.card H).factorization 2 := by
    rw [hk] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hcard : Nat.card V ≤ Nat.card T := by
    rw [natCard_eq_pow_of_isSylow2In hT, ← hfac, hk]
    exact Nat.pow_le_pow_right (by norm_num) hle2
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_of_cover {K L T : Subgroup G} (hLK : L ≤ K)
    (hcov : ∀ x ∈ K, ∃ i ∈ L, ∃ n ∈ oddCoreOf K, x = i * n) (hT : IsSylow2In T L) :
    IsSylow2In T K := by
  have hcov' : ∀ h : ↥K, ∃ i ∈ L.subgroupOf K, ∃ n ∈ classicalInvolutionOddCore ↥K, h = i * n := by
    intro h
    obtain ⟨i, hi, n, hn, hx⟩ := hcov h h.2
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨⟨i, hLK hi⟩, hi, n', hn', Subtype.ext hx⟩
  have h1 := isSylow2In_top_of_cover (CFSG.ComponentClassification.OddCore.odd_card ↥K) hcov'
    (hT.subgroupOf hLK)
  have h2 := isSylow2In_map_subtype_iff.mpr h1
  rwa [Subgroup.map_subgroupOf_eq_of_le (hT.1.trans hLK), Subgroup.map_top,
    Subgroup.range_subtype] at h2

theorem iSup_isSylow2In_eq {L : Subgroup G} (hL : Group.IsPerfect ↥L) :
    (⨆ (P : Subgroup G) (_ : IsSylow2In P L), P) = L := by
  classical
  set M : Subgroup G := ⨆ (P : Subgroup G) (_ : IsSylow2In P L), P with hM
  have hML : M ≤ L := iSup₂_le fun P hP => hP.1
  have hconj : ∀ g : ↥L, conjSub (g : G) M ≤ M := by
    intro g
    unfold conjSub
    rw [hM, Subgroup.map_iSup]
    refine iSup_le fun P => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hP => ?_
    have hP' : IsSylow2In (conjSub (g : G) P) (conjSub (g : G) L) := hP.conj g
    rw [conjSub_eq_self_of_mem g.2] at hP'
    exact le_iSup₂_of_le (conjSub (g : G) P) hP' le_rfl
  have hnorm : (M.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj g (conj_mem_conjSub hn)
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ L)
  have hVM : V ≤ M := le_iSup₂_of_le V hV le_rfl
  have hodd : Odd (M.subgroupOf L).index := by
    have h1 : (M.subgroupOf L).index ∣ (V.subgroupOf L).index :=
      Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono L hVM)
    have h2 : ¬ 2 ∣ (AscQuot.sylowOfIsSylow2In' hV : Subgroup ↥L).index :=
      Sylow.not_dvd_index (AscQuot.sylowOfIsSylow2In' hV)
    have h3 : ¬ 2 ∣ (V.subgroupOf L).index := h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (fun h => h3 (h.trans h1)))
  have : Group.IsPerfect ↥L := hL
  have := hnorm
  have hQodd : Odd (Nat.card (↥L ⧸ M.subgroupOf L)) := by
    rw [← Subgroup.index_eq_card]
    exact hodd
  have hQsolv : Group.IsSolvable (↥L ⧸ M.subgroupOf L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
  have hQsub : Subsingleton (↥L ⧸ M.subgroupOf L) := by
    by_contra hns
    have : Nontrivial (↥L ⧸ M.subgroupOf L) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ M.subgroupOf L) hQsolv
  have hidx : (M.subgroupOf L).index = 1 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_eq_one_iff_unique.mpr ⟨hQsub, ⟨1⟩⟩
  have htop : M.subgroupOf L = ⊤ := Subgroup.index_eq_one.mp hidx
  refine le_antisymm hML fun x hx => ?_
  have hx' : (⟨x, hx⟩ : ↥L) ∈ M.subgroupOf L := htop ▸ Subgroup.mem_top _
  exact hx'

end SylowCover

section LayerSylow

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem layerRes_le_inf (x : G) (K : Subgroup G) : layerRes x K ≤ K ⊓ cenZ x :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem layerRes_le (x : G) (K : Subgroup G) : layerRes x K ≤ K :=
  (layerRes_le_inf x K).trans inf_le_left

omit [Finite G] in
theorem layerRes_le_cenZ (x : G) (K : Subgroup G) : layerRes x K ≤ cenZ x :=
  (layerRes_le_inf x K).trans inf_le_right

theorem XMem.isSylow2In_of_layerRes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {x : G} (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) {T : Subgroup G}
    (hT : IsSylow2In T (layerRes x K)) : IsSylow2In T K := by
  obtain ⟨z, hz⟩ := hΩ.classical K h.1
  exact isSylow2In_of_cover (layerRes_le x K) (h.axisResidual hp hq hΩ hx hz).cover hT

theorem XMem.layerRes_le_rLayer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K : Subgroup G} (h : XMem Ω x K) : layerRes x K ≤ rLayer Ω x := by
  have hL : Group.IsPerfect ↥(layerRes x K) := finite_perfectResidualOf_isPerfect (K ⊓ cenZ x)
  refine le_of_eq_of_le (iSup_isSylow2In_eq hL).symm (iSup₂_le fun P hP => ?_)
  have hPK := h.isSylow2In_of_layerRes hp hq hΩ hx hP
  have hPR : P ∈ RSet Ω := mem_RSet_of_isSylow2In h.1 hPK
  have hPC : P ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← cenZ_eq_centralizer]
    exact hP.1.trans (layerRes_le_cenZ x K)
  unfold rLayer
  exact le_iSup₂_of_le P hPR (le_iSup_of_le hPC le_rfl)

end LayerSylow


end T8

end CFSG.ClassicalInvolution.Asc77
