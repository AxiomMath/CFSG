module

public import CFSG.Open.FusionDefs
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransferDerived
public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem mem_map_conj_inv_iff (L : Subgroup H) (g x : H) :
    x ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem piCore_eq_bot_of_isSubnormal {π : Set Nat.Primes} (hcore : CFSG.piCore π H = ⊥)
    {K : Subgroup H} (hK : K.IsSubnormal) : CFSG.piCore π K = ⊥ := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection π hK
  rwa [hcore, inf_bot_eq, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h

theorem sylow_eq_bot_of_le_center {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {ℓ : ℕ} [Fact ℓ.Prime] (T : Sylow ℓ E) (hT : (T : Subgroup E) ≤ Subgroup.center E) :
    (T : Subgroup E) = ⊥ := by
  have hcomm : ⁅(T : Subgroup E), (T : Subgroup E)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hT.trans (Subgroup.center_le_centralizer _))
  have := (CFSG.ShultStronglyClosedTI.MiscAlgebra.central_sylow_transfer_derived T _ hT
    T.isPGroup').1
  rwa [hcomm, le_bot_iff] at this

theorem eq_bot_of_isSubnormal_of_isPiSubgroup {π : Set Nat.Primes} (hcore : CFSG.piCore π H = ⊥)
    {K : Subgroup H} (hK : K.IsSubnormal) (hπ : CFSG.IsPiSubgroup π K) : K = ⊥ := by
  have htop : CFSG.piCore π K = ⊤ :=
    top_le_iff.mp (CFSG.LocalCores.le_piCore_of_normal inferInstance
      (by rwa [CFSG.IsPiSubgroup, Subgroup.card_top]))
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection π hK
  rwa [htop, Subgroup.map_top, Subgroup.range_subtype, hcore, inf_bot_eq] at h

theorem central_sylow_normalizes_components {p : ℕ} [Fact p.Prime]
    (hcore : CFSG.pPrimeCore p H = ⊥) (S : Sylow p H) {z : H}
    (hz : z ∈ Subgroup.centralizer ((S : Subgroup H) : Set H)) (hzS : z ∈ (S : Subgroup H))
    {L : Subgroup H} (hL : CFSG.IsComponent L) : z ∈ Subgroup.normalizer (L : Set H) := by
  have _hzS := hzS
  by_contra hnorm
  let M : Subgroup H := L.map (MulAut.conj z⁻¹).toMonoidHom
  have hmemM : ∀ x : H, x ∈ M ↔ z * x * z⁻¹ ∈ L := mem_map_conj_inv_iff L z
  have hM : CFSG.IsComponent M := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z⁻¹) hL
  have hne : L ≠ M := fun h =>
    hnorm (Subgroup.mem_normalizer_iff.mpr fun x => (SetLike.ext_iff.mp h x).trans (hmemM x))
  have hLM : ⁅L, M⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hM).resolve_left hne
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_inf_of_subnormal S hL.2
  have : Group.IsPerfect L := hL.1.1
  have hTZ : (T : Subgroup L) ≤ Subgroup.center L := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    have htS : (t : H) ∈ (S : Subgroup H) ⊓ L := hT ▸ Subgroup.mem_map_of_mem _ ht
    have hfix : z * (t : H) * z⁻¹ = t := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hz t htS.1).symm
    have htM : (t : H) ∈ M := (hmemM t).mpr (by rw [hfix]; exact t.2)
    have hg := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLM g.2) t htM
    exact Subtype.ext hg.symm
  have hT1 := sylow_eq_bot_of_le_center T hTZ
  have hπ : CFSG.IsPiSubgroup {q : Nat.Primes | q.val ≠ p} L := fun q hq hqp =>
    T.ne_bot_of_dvd_card (hqp ▸ hq) hT1
  have hcore' : CFSG.piCore {q : Nat.Primes | q.val ≠ p} H = ⊥ := by
    rw [← CFSG.pPrimeCore_eq_piCore]
    exact hcore
  have hLbot := eq_bot_of_isSubnormal_of_isPiSubgroup hcore' hL.2 hπ
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  exact hx (Subtype.ext (Subgroup.mem_bot.mp (hLbot ▸ x.2)))

theorem quasisimple_quotient_even_of_oddCore_eq_bot {L : Type*} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) (hcore : CFSG.oddCore L = ⊥) :
    Even (Nat.card (L ⧸ Subgroup.center L)) := by
  by_contra hodd
  have hodd' : Odd (Nat.card (L ⧸ Subgroup.center L)) := Nat.not_even_iff_odd.mp hodd
  have : Group.IsPerfect L := hL.1
  let T : Sylow 2 L := default
  have hTZ : (T : Subgroup L) ≤ Subgroup.center L := by
    have hbar : Nat.card ((T : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L))) = 1 := by
      rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) T,
        Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hodd'.not_two_dvd_nat,
        pow_zero]
    rwa [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbar
  have hT1 := sylow_eq_bot_of_le_center T hTZ
  have hodd2 : Odd (Nat.card L) :=
    Nat.not_even_iff_odd.mp fun heven => T.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven) hT1
  have hle : (⊤ : Subgroup L) ≤ CFSG.oddCore L :=
    le_sSup ⟨inferInstance, by rw [Subgroup.card_top]; exact hodd2⟩
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  have hxbot : x ∈ (⊥ : Subgroup L) := hcore ▸ hle (Subgroup.mem_top x)
  exact hx (Subgroup.mem_bot.mp hxbot)

theorem simple_sylow_normalizer_commutator_ne_bot {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hnonab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (hP : (P : Subgroup K) ≠ ⊥) :
    ⁅(P : Subgroup K), Subgroup.normalizer ((P : Subgroup K) : Set K)⁆ ≠ ⊥ := by
  intro hcomm
  have hnorm : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := by
    intro n hn x hx
    have hmem : ⁅x, n⁆ ∈ ⁅(P : Subgroup K), Subgroup.normalizer ((P : Subgroup K) : Set K)⁆ :=
      Subgroup.commutator_mem_commutator hx hn
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  obtain ⟨N, hNn, -, hNindex, -, -, -, -, -, -, hab⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hnorm
  have hNtop : N ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hNindex
    exact hP (Subgroup.card_eq_one.mp hNindex.symm)
  have : N.Normal := hNn
  have hNbot : N = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right hNtop
  obtain ⟨a, b, hab'⟩ := hnonab
  apply hab'
  have h := hab (a : K ⧸ N) (b : K ⧸ N)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNbot,
    Subgroup.mem_bot] at h
  have h' : (a * b)⁻¹ * (b * a) = 1 := h
  rw [inv_mul_eq_one] at h'
  exact h'

theorem isPGroup_two_center_of_oddCore_eq_bot {Q : Type*} [Group Q] [Finite Q]
    (hcore : CFSG.oddCore Q = ⊥) : IsPGroup 2 (Subgroup.center Q) := by
  intro z
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : Q)).ne'
  refine ⟨k, Subtype.ext ?_⟩
  have hy : orderOf ((z : Q) ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (hord ▸ dvd_mul_right _ _), hord,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hyc : (z : Q) ^ 2 ^ k ∈ Subgroup.center Q := Subgroup.pow_mem _ z.2 _
  have hzp : Subgroup.zpowers ((z : Q) ^ 2 ^ k) ≤ Subgroup.center Q :=
    (Subgroup.zpowers_le).mpr hyc
  have hnormal : (Subgroup.zpowers ((z : Q) ^ 2 ^ k)).Normal := Subgroup.normal_of_le_center hzp
  have hle : Subgroup.zpowers ((z : Q) ^ 2 ^ k) ≤ CFSG.oddCore Q :=
    le_sSup ⟨hnormal, by rwa [Nat.card_zpowers, hy]⟩
  rw [hcore, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact_mod_cast hle

omit [Finite H] in
theorem mul_inv_conj_mem_of_stronglyClosed {S U : Subgroup H} (hUS : U ≤ S)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hclosed : fusionStronglyClosed (U : Set H) S)
    {K M : Subgroup H} (hKM : ∀ k ∈ K, ∀ m ∈ M, k * m = m * k) {a : H} (ha : a ∈ U)
    (haM : ∀ x ∈ K, a⁻¹ * x * a ∈ M) {v n : H} (hvS : v ∈ S) (hvK : v ∈ K) (hnK : n ∈ K)
    (hvn : n⁻¹ * v * n ∈ S) : v * (n⁻¹ * v * n)⁻¹ ∈ M := by
  set m : H := a⁻¹ * v * a with hm
  have hmM : m ∈ M := haM v hvK
  have hmS : m ∈ S := S.mul_mem (S.mul_mem (S.inv_mem (hUS ha)) hvS) (hUS ha)
  have hd : v⁻¹ * m ∈ U := by
    have h1 : v⁻¹ * a⁻¹ * v ∈ U := hclosed a⁻¹ (U.inv_mem ha) v
      (S.mul_mem (S.mul_mem (S.inv_mem hvS) (S.inv_mem (hUS ha))) hvS)
    have h2 : v⁻¹ * m = (v⁻¹ * a⁻¹ * v) * a := by rw [hm]; group
    rw [h2]
    exact U.mul_mem h1 ha
  have hmn : n * m = m * n := hKM n hnK m hmM
  have hnm : n⁻¹ * m * n = m := by rw [mul_assoc, ← hmn, inv_mul_cancel_left]
  have hd' : n⁻¹ * (v⁻¹ * m) * n = (n⁻¹ * v * n)⁻¹ * m := by
    calc n⁻¹ * (v⁻¹ * m) * n = (n⁻¹ * v * n)⁻¹ * (n⁻¹ * m * n) := by group
      _ = (n⁻¹ * v * n)⁻¹ * m := by rw [hnm]
  have hd'S : n⁻¹ * (v⁻¹ * m) * n ∈ S := by
    rw [hd']
    exact S.mul_mem (S.inv_mem hvn) hmS
  have hd'U : n⁻¹ * (v⁻¹ * m) * n ∈ U := hclosed _ hd n hd'S
  have heU : (v⁻¹ * m)⁻¹ * (n⁻¹ * (v⁻¹ * m) * n) ∈ U := U.mul_mem (U.inv_mem hd) hd'U
  have hwK : v * (n⁻¹ * v * n)⁻¹ ∈ K :=
    K.mul_mem hvK (K.inv_mem (K.mul_mem (K.mul_mem (K.inv_mem hnK) hvK) hnK))
  have hwm : v * (n⁻¹ * v * n)⁻¹ * m = m * (v * (n⁻¹ * v * n)⁻¹) := hKM _ hwK m hmM
  have he : (v⁻¹ * m)⁻¹ * (n⁻¹ * (v⁻¹ * m) * n) = v * (n⁻¹ * v * n)⁻¹ := by
    rw [hd']
    calc (v⁻¹ * m)⁻¹ * ((n⁻¹ * v * n)⁻¹ * m) = m⁻¹ * (v * (n⁻¹ * v * n)⁻¹ * m) := by group
      _ = m⁻¹ * (m * (v * (n⁻¹ * v * n)⁻¹)) := by rw [hwm]
      _ = v * (n⁻¹ * v * n)⁻¹ := inv_mul_cancel_left _ _
  rw [he] at heU
  have hcomm := hUab a ha _ heU
  have hconj : a⁻¹ * (v * (n⁻¹ * v * n)⁻¹) * a = v * (n⁻¹ * v * n)⁻¹ := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have := haM _ hwK
  rwa [hconj] at this

theorem false_of_sylow_normalizer_commutator_mem_center {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hcore : CFSG.oddCore Q = ⊥) (T : Sylow 2 Q)
    (hZT : Subgroup.center Q ≤ (T : Subgroup Q))
    (hcomm : ∀ t ∈ (T : Subgroup Q), ∀ n ∈ Subgroup.normalizer ((T : Subgroup Q) : Set Q),
      t * (n⁻¹ * t * n)⁻¹ ∈ Subgroup.center Q) : False := by
  have hev := quasisimple_quotient_even_of_oddCore_eq_bot hQ hcore
  obtain ⟨-, hsimple, hnonab⟩ := hQ
  let Tb : Sylow 2 (Q ⧸ Subgroup.center Q) :=
    T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have hTb : (Tb : Subgroup (Q ⧸ Subgroup.center Q)) =
      (T : Subgroup Q).map (QuotientGroup.mk' (Subgroup.center Q)) :=
    Sylow.coe_mapSurjective _ T
  have hTbne : (Tb : Subgroup (Q ⧸ Subgroup.center Q)) ≠ ⊥ :=
    Tb.ne_bot_of_dvd_card (even_iff_two_dvd.mp hev)
  have key : ∀ n : Q, (n : Q ⧸ Subgroup.center Q) ∈
      Subgroup.normalizer ((Tb : Subgroup (Q ⧸ Subgroup.center Q)) : Set (Q ⧸ Subgroup.center Q)) →
      ∀ h ∈ (T : Subgroup Q), n * h * n⁻¹ ∈ (T : Subgroup Q) := by
    intro n hn h hh
    have hh' : (h : Q ⧸ Subgroup.center Q) ∈ (Tb : Subgroup (Q ⧸ Subgroup.center Q)) := by
      rw [hTb]
      exact ⟨h, hh, rfl⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mp hh'
    rw [hTb] at h2
    obtain ⟨t', ht', heq⟩ := h2
    have h3 : (t' : Q ⧸ Subgroup.center Q) = ((n * h * n⁻¹ : Q) : Q ⧸ Subgroup.center Q) := by
      simpa using heq
    have hmem : t'⁻¹ * (n * h * n⁻¹) ∈ Subgroup.center Q := QuotientGroup.eq.mp h3
    have h4 : n * h * n⁻¹ = t' * (t'⁻¹ * (n * h * n⁻¹)) := by group
    rw [h4]
    exact (T : Subgroup Q).mul_mem ht' (hZT hmem)
  refine simple_sylow_normalizer_commutator_ne_bot hnonab Tb hTbne ?_
  rw [← le_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [hTb] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  have hnT : n ∈ Subgroup.normalizer ((T : Subgroup Q) : Set Q) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key n hy h, fun hh => ?_⟩
    have hinv : ((n⁻¹ : Q) : Q ⧸ Subgroup.center Q) ∈ Subgroup.normalizer
        ((Tb : Subgroup (Q ⧸ Subgroup.center Q)) : Set (Q ⧸ Subgroup.center Q)) := by
      rw [QuotientGroup.mk_inv]
      exact inv_mem hy
    have h5 := key n⁻¹ hinv _ hh
    have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
    rwa [e] at h5
  have h1 : ((t * (n⁻¹ * t * n)⁻¹ : Q) : Q ⧸ Subgroup.center Q) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hcomm t ht n hnT)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h1
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  change (t : Q ⧸ Subgroup.center Q) * n = n * t
  calc (t : Q ⧸ Subgroup.center Q) * n = n * ((n : Q ⧸ Subgroup.center Q)⁻¹ * t * n) := by group
    _ = n * t := by rw [← h1]

theorem false_of_commute_conj_of_stronglyClosed (S : Sylow 2 H) {U : Subgroup H}
    (hUS : U ≤ (S : Subgroup H)) (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hclosed : fusionStronglyClosed (U : Set H) (S : Subgroup H)) {K : Subgroup H}
    (hKsn : K.IsSubnormal) (hKq : CFSG.IsQuasisimple K) (hKodd : CFSG.oddCore K = ⊥) {a : H}
    (ha : a ∈ U)
    (hKM : ∀ k ∈ K, ∀ m ∈ K.map (MulAut.conj a⁻¹).toMonoidHom, k * m = m * k) : False := by
  have haM : ∀ x ∈ K, a⁻¹ * x * a ∈ K.map (MulAut.conj a⁻¹).toMonoidHom := fun x hx =>
    (mem_map_conj_inv_iff K a _).mpr (by simpa [mul_assoc] using hx)
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_inf_of_subnormal S hKsn
  have hTmem : ∀ t : K, t ∈ (T : Subgroup K) ↔ (t : H) ∈ (S : Subgroup H) := by
    intro t
    constructor
    · intro ht
      have : (t : H) ∈ (S : Subgroup H) ⊓ K := hT ▸ Subgroup.mem_map_of_mem _ ht
      exact this.1
    · intro ht
      have : (t : H) ∈ (T : Subgroup K).map K.subtype := by
        rw [hT]
        exact ⟨ht, t.2⟩
      obtain ⟨t', ht', heq⟩ := this
      have : t' = t := Subtype.ext heq
      rwa [← this]
  have hZT : Subgroup.center K ≤ (T : Subgroup K) :=
    (isPGroup_two_center_of_oddCore_eq_bot hKodd).le_sylow_of_normal T
  refine false_of_sylow_normalizer_commutator_mem_center hKq hKodd T hZT ?_
  intro t ht n hn
  have hn' : n⁻¹ * t * n ∈ (T : Subgroup K) := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer ((T : Subgroup K) : Set K)).inv_mem hn) t).mp ht
    simpa using this
  have hmain := mul_inv_conj_mem_of_stronglyClosed (S := (S : Subgroup H)) hUS hUab hclosed
    (K := K) hKM ha haM ((hTmem t).mp ht) t.2 n.2 ((hTmem _).mp hn')
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (hKM g g.2 _ hmain)

theorem oddCore_eq_bot_of_isSimpleGroup_of_even {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (heven : Even (Nat.card Q)) : CFSG.oddCore Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore Q) with h | h
  · exact h
  · exfalso
    have hπ := CFSG.LocalCores.piCore_isPiSubgroup (G := Q) {q : Nat.Primes | q.val ≠ 2}
    rw [← CFSG.oddCore_eq_piCore, h, CFSG.IsPiSubgroup, Subgroup.card_top] at hπ
    exact hπ ⟨2, Nat.prime_two⟩ (even_iff_two_dvd.mp heven) rfl

omit [Finite H] in
theorem isSubnormal_of_commuting_family {ι : Type*} (K : ι → Subgroup H)
    (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥)
    (hperm : ∀ g : H, ∀ i, ∃ j, (K i).map (MulAut.conj g⁻¹).toMonoidHom = K j) (i : ι) :
    (K i).IsSubnormal := by
  have hN : (⨆ j, K j).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hle : (⨆ j, K j).map (MulAut.conj g).toMonoidHom ≤ ⨆ j, K j := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      obtain ⟨j', hj'⟩ := hperm g⁻¹ j
      rw [inv_inv] at hj'
      rw [hj']
      exact le_iSup K j'
    exact hle ⟨x, hx, rfl⟩
  have hnorm : ⨆ j, K j ≤ Subgroup.normalizer (K i : Set H) := by
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm j i hij)).trans
        (Subgroup.centralizer_le_normalizer _)
  exact Subgroup.IsSubnormal.step (K i) (⨆ j, K j) (le_iSup K i) hN.isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup K i)).mpr hnorm)

theorem strongly_closed_normalizes_simple_factors {ι : Type*} (S : Sylow 2 H) {A : Subgroup H}
    (hAS : A ≤ (S : Subgroup H)) (hA : IsElemAbelian 2 A)
    (hclosed : fusionStronglyClosed (A : Set H) (S : Subgroup H)) (K : ι → Subgroup H)
    (hsimple : ∀ i, IsSimpleGroup (K i)) (hnonab : ∀ i, ∃ a b : K i, a * b ≠ b * a)
    (heven : ∀ i, Even (Nat.card (K i))) (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥)
    (hperm : ∀ g : H, ∀ i, ∃ j, (K i).map (MulAut.conj g⁻¹).toMonoidHom = K j) (i : ι) :
    A ≤ Subgroup.normalizer (K i : Set H) := by
  intro a ha
  by_contra hna
  obtain ⟨j, hj⟩ := hperm a i
  have hji : j ≠ i := by
    rintro rfl
    exact hna (Subgroup.mem_normalizer_iff.mpr fun x =>
      (SetLike.ext_iff.mp hj x).symm.trans (mem_map_conj_inv_iff _ a x))
  have := hsimple i
  have hKM : ∀ k ∈ K i, ∀ m ∈ (K i).map (MulAut.conj a⁻¹).toMonoidHom, k * m = m * k := by
    rw [hj]
    intro k hk m hm
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hji.symm) hk) m hm).symm
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact false_of_commute_conj_of_stronglyClosed S hAS hAab hclosed
    (isSubnormal_of_commuting_family K hcomm hperm i)
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hnonab i)).1
    (oddCore_eq_bot_of_isSimpleGroup_of_even (heven i)) ha hKM

theorem strongly_closed_normalizes_components (hcore : CFSG.oddCore H = ⊥) (S : Sylow 2 H)
    {U : Subgroup H} (hUS : U ≤ (S : Subgroup H)) (hU : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set H) (S : Subgroup H)) {L : Subgroup H}
    (hL : CFSG.IsComponent L) : U ≤ Subgroup.normalizer (L : Set H) := by
  intro a ha
  by_contra hna
  let M : Subgroup H := L.map (MulAut.conj a⁻¹).toMonoidHom
  have hmemM : ∀ x : H, x ∈ M ↔ a * x * a⁻¹ ∈ L := mem_map_conj_inv_iff L a
  have hM : CFSG.IsComponent M := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj a⁻¹) hL
  have hne : L ≠ M := fun h =>
    hna (Subgroup.mem_normalizer_iff.mpr fun x => (SetLike.ext_iff.mp h x).trans (hmemM x))
  have hLM : ⁅L, M⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hM).resolve_left hne
  have hKM : ∀ k ∈ L, ∀ m ∈ M, k * m = m * k := fun k hk m hm =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLM hk) m hm).symm
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLodd : CFSG.oddCore L = ⊥ := by
    have h1 : CFSG.piCore {q : Nat.Primes | q.val ≠ 2} H = ⊥ := by
      rw [← CFSG.oddCore_eq_piCore]
      exact hcore
    rw [CFSG.oddCore_eq_piCore]
    exact piCore_eq_bot_of_isSubnormal h1 hL.2
  exact false_of_commute_conj_of_stronglyClosed S hUS hUab hclosed hL.2 hL.1 hLodd ha hKM

end CFSG.QuasithinUnique
