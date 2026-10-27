module

public import CFSG.GH74.Generic.S45.Defs
public import CFSG.GH74.Generic.S45.RankLemmas
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.ABGLocalTools Subgroup

section Algebra

theorem sylow_le_sup_centralizer {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hAut : AutTwoInner ↥K) {P : Subgroup X} (hP : IsPGroup 2 ↥P) :
    P ≤ K ⊔ centralizer (K : Set X) := by
  intro t ht
  let ψ : X →* MulAut ↥K := MulAut.conjNormal
  have hpow : IsPGroup 2 ↥(zpowers (ψ t)) := by
    have h1 : IsPGroup 2 ↥(P.map ψ) := hP.map ψ
    have h2 : zpowers (ψ t) ≤ P.map ψ := by
      rw [zpowers_le]; exact ⟨t, ht, rfl⟩
    exact h1.to_le h2
  obtain ⟨k, hk⟩ := hAut (ψ t) hpow
  have hψk : ψ (k : X) = MulAut.conj k := by
    ext l
    simp [ψ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hker : t * (k : X)⁻¹ ∈ centralizer (K : Set X) := by
    have h3 : ψ (t * (k : X)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψk, hk]
      exact mul_inv_cancel _
    rw [mem_centralizer_iff]
    intro l hl
    have h4 := congrArg (fun a : MulAut ↥K => (a ⟨l, hl⟩ : X)) h3
    simp only [ψ, MulAut.conjNormal_apply, MulAut.one_apply] at h4
    have h5 : (t * (k : X)⁻¹) * l * (t * (k : X)⁻¹)⁻¹ = l := h4
    calc l * (t * (k : X)⁻¹) = ((t * (k : X)⁻¹) * l * (t * (k : X)⁻¹)⁻¹) * (t * (k : X)⁻¹) := by
          rw [h5]
      _ = (t * (k : X)⁻¹) * l := by group
  have : t = (t * (k : X)⁻¹) * (k : X) := by group
  rw [this]
  exact mul_mem (mem_sup_right hker) (mem_sup_left k.2)

theorem card_sup_normal {X : Type*} [Group X] [Finite X] {A D : Subgroup X} [D.Normal]
    (hAD : A ⊓ D = ⊥) : Nat.card ↥(A ⊔ D) = Nat.card ↥A * Nat.card ↥D := by
  have h := relIndex_sup_eq_relIndex_of_normal D A
  rw [sup_comm] at h
  have h1 := Subgroup.relIndex_mul_card A (A ⊔ D)
  rw [inf_eq_left.mpr (le_sup_left : A ≤ A ⊔ D)] at h1
  have h2 : A.relIndex D = Nat.card ↥D := by
    have : A.subgroupOf D = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      have hdA : (d : X) ∈ A := hd
      have hdD : (d : X) ∈ D := d.2
      have : (d : X) ∈ A ⊓ D := ⟨hdA, hdD⟩
      rw [hAD, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    unfold Subgroup.relIndex
    rw [this, Subgroup.index_bot]
  rw [h, h2] at h1
  rw [← h1]
  ring

theorem isPGroup_sup_of_commute {X : Type*} [Group X] {R D : Subgroup X} [D.Normal]
    (hD : IsPGroup 2 ↥D) (hR : IsPGroup 2 ↥R) (hcomm : ∀ r ∈ R, ∀ d ∈ D, r * d = d * r) :
    IsPGroup 2 ↥(R ⊔ D) := by
  intro g
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 g.2
  obtain ⟨a, ha⟩ := hR ⟨y, hy⟩
  obtain ⟨b, hb⟩ := hD ⟨z, hz⟩
  have ha' : y ^ (2 ^ a) = 1 := congrArg Subtype.val ha
  have hb' : z ^ (2 ^ b) = 1 := congrArg Subtype.val hb
  refine ⟨a + b, Subtype.ext ?_⟩
  change (g : X) ^ (2 ^ (a + b)) = 1
  rw [← hyz]
  have hc : Commute y z := hcomm y hy z hz
  rw [hc.mul_pow]
  have h1 : y ^ (2 ^ (a + b)) = 1 := by
    rw [pow_add, pow_mul, ha', one_pow]
  have h2 : z ^ (2 ^ (a + b)) = 1 := by
    rw [add_comm, pow_add, pow_mul, hb', one_pow]
  rw [h1, h2, one_mul]

theorem sup_isSylow {X : Type} [Group X] [Finite X] {K D R : Subgroup X} [D.Normal]
    (hD : IsPGroup 2 ↥D) (hKD : K ⊓ D = ⊥) (hcomm : ∀ r ∈ R, ∀ d ∈ D, r * d = d * r)
    (hR : IsPGroup 2 ↥R) (hRK : R ≤ K) (hRsyl : ¬ 2 ∣ R.relIndex K)
    (hsyl : ∀ T : Sylow 2 X, (T : Subgroup X) ≤ K ⊔ D) :
    IsPGroup 2 ↥(R ⊔ D) ∧ ¬ 2 ∣ (R ⊔ D).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ := isPGroup_sup_of_commute hD hR hcomm
  refine ⟨hS₀, ?_⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hTp : IsPGroup 2 ↥(T : Subgroup X) := T.isPGroup'
  have hDT : D ≤ (T : Subgroup X) := hD.le_sylow_of_normal T
  have hTle := hsyl T
  have hTeq : (T : Subgroup X) = ((T : Subgroup X) ⊓ K) ⊔ D := by
    apply le_antisymm
    · intro t ht
      obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_right.1 (hTle ht)
      have hkT : k ∈ (T : Subgroup X) := by
        have : k = t * d⁻¹ := by rw [← hkd]; group
        rw [this]; exact mul_mem ht (inv_mem (hDT hd))
      rw [← hkd]
      exact mul_mem (mem_sup_left ⟨hkT, hk⟩) (mem_sup_right hd)
    · exact sup_le inf_le_left hDT
  have hTKD : (T : Subgroup X) ⊓ K ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ K ⊓ D := ⟨hg.1.2, hg.2⟩
    rw [hKD] at this
    exact this
  have hcT : Nat.card ↥(T : Subgroup X) = Nat.card ↥((T : Subgroup X) ⊓ K) * Nat.card ↥D := by
    conv_lhs => rw [hTeq]
    exact card_sup_normal hTKD
  have hRD : R ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ K ⊓ D := ⟨hRK hg.1, hg.2⟩
    rw [hKD] at this
    exact this
  have hcS : Nat.card ↥(R ⊔ D) = Nat.card ↥R * Nat.card ↥D := card_sup_normal hRD
  have hle : Nat.card ↥((T : Subgroup X) ⊓ K) ≤ Nat.card ↥R := by
    have hTK : IsPGroup 2 ↥((T : Subgroup X) ⊓ K) := hTp.to_le inf_le_left
    have hP' : IsPGroup 2 ↥(((T : Subgroup X) ⊓ K).subgroupOf K) := hTK.comap_subtype
    have hR' : IsPGroup 2 ↥(R.subgroupOf K) := hR.comap_subtype
    let R' : Sylow 2 ↥K := hR'.toSylow hRsyl
    obtain ⟨Q', hQ'⟩ := hP'.exists_le_sylow
    have h1 : Nat.card ↥(((T : Subgroup X) ⊓ K).subgroupOf K) ≤ Nat.card ↥(Q' : Subgroup ↥K) :=
      Subgroup.card_le_of_le hQ'
    have h2 : Nat.card ↥(Q' : Subgroup ↥K) = Nat.card ↥(R' : Subgroup ↥K) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have h3 : Nat.card ↥(R' : Subgroup ↥K) = Nat.card ↥R := by
      rw [show (R' : Subgroup ↥K) = R.subgroupOf K from rfl]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
    have h4 : Nat.card ↥(((T : Subgroup X) ⊓ K).subgroupOf K) =
        Nat.card ↥((T : Subgroup X) ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    omega
  have hle2 : Nat.card ↥(R ⊔ D) ≤ Nat.card ↥(T : Subgroup X) := by
    obtain ⟨T', hT'⟩ := hS₀.exists_le_sylow
    have h1 : Nat.card ↥(R ⊔ D) ≤ Nat.card ↥(T' : Subgroup X) := Subgroup.card_le_of_le hT'
    have h2 : Nat.card ↥(T' : Subgroup X) = Nat.card ↥(T : Subgroup X) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    omega
  have hD0 : 0 < Nat.card ↥D := Nat.card_pos
  have hSeq : Nat.card ↥(R ⊔ D) = Nat.card ↥(T : Subgroup X) := by
    apply le_antisymm hle2
    rw [hcT, hcS]
    exact Nat.mul_le_mul_right _ hle
  have h5 := Subgroup.card_mul_index (R ⊔ D)
  have h6 := Subgroup.card_mul_index (T : Subgroup X)
  rw [hSeq] at h5
  have hpos : 0 < Nat.card ↥(T : Subgroup X) := Nat.card_pos
  have : (R ⊔ D).index = (T : Subgroup X).index := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h5, h6]
  rw [this]
  exact T.not_dvd_index

theorem eq_of_involutions_cyclic {X : Type*} [Group X] {D : Subgroup X} (hD : IsCyclic ↥D)
    [Finite D] {a b : X} (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha2 : a * a = 1) (hb2 : b * b = 1) : a = b := by
  classical
  by_contra hab
  have : Fintype D := Fintype.ofFinite D
  have hle := IsCyclic.card_pow_eq_one_le (α := D) (n := 2) (by norm_num)
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset D) ⊆ Finset.univ.filter (fun g : D => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hg with rfl | rfl | rfl
    · simp
    · exact Subtype.ext (by simpa [pow_two] using ha2)
    · exact Subtype.ext (by simpa [pow_two] using hb2)
  have hcard : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset D).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      apply hab
      exact congrArg Subtype.val h
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_sq_of_cyclic_two_group {X : Type*} [Group X] {D : Subgroup X} [Finite D]
    (hD : IsCyclic ↥D) (hD2 : IsPGroup 2 ↥D) {z : X} (hz : z ∈ D) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hcard : Nat.card ↥D ≠ 2) : ∃ e ∈ D, e * e = z := by
  obtain ⟨d, hd⟩ := hD
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have hord : orderOf d = 2 ^ k := (orderOf_eq_card_of_forall_mem_zpowers hd).trans hk
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · exfalso
      have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D (by simpa using hk)
      rw [hbot, Subgroup.mem_bot] at hz
      exact hz1 hz
    · exact absurd (by simpa using hk) hcard
    · omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hw1 : d ^ (2 ^ (m + 1)) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · positivity
    · rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw2 : (d ^ (2 ^ (m + 1))) * (d ^ (2 ^ (m + 1))) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hord]
    exact pow_orderOf_eq_one d
  have hzw : z = ((d ^ (2 ^ (m + 1)) : ↥D) : X) :=
    eq_of_involutions_cyclic (D := D) ⟨d, hd⟩ hz (Subtype.mem _) hz1
      (fun h => hw1 (Subtype.ext h)) hzz
      (by simpa using congrArg Subtype.val hw2)
  refine ⟨((d ^ (2 ^ m) : ↥D) : X), Subtype.mem _, ?_⟩
  rw [hzw, ← Subgroup.coe_mul, ← pow_add, ← two_mul, ← pow_succ']

end Algebra

structure KData (X : Type) [Group X] [Finite X] (K : Subgroup X) (z : X) : Prop where
  gen4 : Gen4 X
  oddcore : pPrimeCore 2 X = ⊥
  central : ∀ g : X, g * z = z * g
  sq : z * z = 1
  ne : z ≠ 1
  comp : IsComponent K
  notin : z ∉ K
  facts : KBase ↥K

namespace KData

variable {X : Type} [Group X] [Finite X] {K : Subgroup X} {z : X}

theorem center_trivial (h : KData X K z) : ∀ k ∈ K, (∀ l ∈ K, l * k = k * l) → k = 1 := by
  have hs : IsSimpleGroup ↥K := h.facts.1
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := h.comp.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    refine ⟨a, b, fun h' => hab' ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']
  intro k hk hkc
  have hmem : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hkc g g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : a ∈ Subgroup.center ↥K := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem inf_centralizer_eq_bot (h : KData X K z) : K ⊓ centralizer (K : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact h.center_trivial g hg.1 (fun l hl => (mem_centralizer_iff.1 hg.2 l hl))

theorem cyclic_of_le_centralizer (h : KData X K z) {P : Subgroup X} (hP : IsPGroup 2 ↥P)
    (hPc : P ≤ centralizer (K : Set X)) : IsCyclic ↥P := by
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨hRc, hRsq, hRcard, -⟩ := h.facts.2.2 R
  let R₀ : Subgroup X := (R : Subgroup ↥K).map K.subtype
  have hRcomm : ∀ a b : ↥R₀, a * b = b * a := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    exact Subtype.ext (congrArg (fun u : ↥(R : Subgroup ↥K) => ((u : ↥K) : X))
      (hRc ⟨a, ha⟩ ⟨b, hb⟩))
  have hRsq' : ∀ a : ↥R₀, a * a = 1 := by
    rintro ⟨_, a, ha, rfl⟩
    exact Subtype.ext (congrArg (fun u : ↥(R : Subgroup ↥K) => ((u : ↥K) : X)) (hRsq ⟨a, ha⟩))
  have hcard : Nat.card ↥R₀ = 8 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hRcard
  have hcomm : ∀ r ∈ R₀, ∀ p ∈ P, r * p = p * r := by
    rintro _ ⟨r, -, rfl⟩ p hp
    exact (mem_centralizer_iff.1 (hPc hp) r r.2)
  have hdisj : R₀ ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨⟨r, -, rfl⟩, hgP⟩ := hg
    rw [Subgroup.mem_bot]
    have : (r : X) ∈ K ⊓ centralizer (K : Set X) := ⟨r.2, hPc hgP⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at this
    exact this
  exact isCyclic_of_commuting_e8 h.gen4 hRcomm hRsq' hcard hP hcomm hdisj

theorem component_eq (h : KData X K z) {K' : Subgroup X} (hK' : IsComponent K') : K' = K := by
  by_contra hne
  rcases LocalCores.distinct_components_commute h.comp hK' with h1 | h1
  · exact hne h1.symm
  · have hle : K' ≤ centralizer (K : Set X) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h1
    obtain ⟨P, hP2, hPnc⟩ := exists_noncyclic_two_subgroup_of_quasisimple hK'.1
    have hmap : IsPGroup 2 ↥(P.map K'.subtype) := hP2.map K'.subtype
    have hmapc : P.map K'.subtype ≤ centralizer (K : Set X) := by
      rintro _ ⟨p, -, rfl⟩
      exact hle p.2
    have hcyc := h.cyclic_of_le_centralizer hmap hmapc
    exact hPnc ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective P K'.subtype
      K'.subtype_injective)).2 hcyc)

theorem layer_eq (h : KData X K z) : layer X = K := by
  have hset : {K' : Subgroup X | IsComponent K'} = {K} := by
    ext K'
    exact ⟨fun hK' => h.component_eq hK', fun hK' => hK' ▸ h.comp⟩
  simp only [CFSG.layer.eq_sSup]
  rw [hset, sSup_singleton]

theorem normal (h : KData X K z) : K.Normal := by
  have hch : (layer X).Characteristic := LocalCores.layer_characteristic (G := X)
  have hn : (layer X).Normal := inferInstance
  rwa [h.layer_eq] at hn

theorem z_mem_centralizer (h : KData X K z) : z ∈ centralizer (K : Set X) := by
  rw [mem_centralizer_iff]
  intro k _
  exact h.central k

theorem D_isPGroup_cyclic (h : KData X K z) :
    IsPGroup 2 ↥(centralizer (K : Set X)) ∧ IsCyclic ↥(centralizer (K : Set X)) := by
  have hKn := h.normal
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup X := centralizer (K : Set X) with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  have hSmap : IsPGroup 2 ↥((S : Subgroup ↥D).map D.subtype) := S.isPGroup'.map D.subtype
  have hSle : (S : Subgroup ↥D).map D.subtype ≤ centralizer (K : Set X) := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hSc := h.cyclic_of_le_centralizer hSmap hSle
  have hScyc : IsCyclic ↥(S : Subgroup ↥D) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (S : Subgroup ↥D) D.subtype
      D.subtype_injective)).2 hSc
  obtain ⟨hcard, -, -, -, -⟩ := cyclic_sylow_normal_odd_complement S hScyc
  have hOD : pPrimeCore 2 ↥D = ⊥ := by
    have hnorm : ((pPrimeCore 2 ↥D).map D.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥D).map D.subtype)) := by
      rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥D).map D.subtype ≤ pPrimeCore 2 X := le_sSup ⟨hnorm, hcop⟩
    rw [h.oddcore, le_bot_iff] at hle
    exact Subgroup.map_injective D.subtype_injective (by rw [Subgroup.map_bot]; exact hle)
  rw [hOD, Subgroup.card_bot] at hcard
  have hcS : Nat.card ↥(S : Subgroup ↥D) ∣ Nat.card ↥D := Subgroup.card_subgroup_dvd_card _
  have hDcard : Nat.card ↥D = Nat.card ↥(S : Subgroup ↥D) := by
    obtain ⟨m, hm⟩ := hcS
    have hpos : 0 < Nat.card ↥(S : Subgroup ↥D) := Nat.card_pos
    have hm1 : Nat.card ↥D / Nat.card ↥(S : Subgroup ↥D) = m := by
      rw [hm]; exact Nat.mul_div_cancel_left m hpos
    have hm2 : m = 1 := by omega
    rw [hm, hm2, mul_one]
  have hStop : (S : Subgroup ↥D) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hDcard.symm
  have e : ↥(S : Subgroup ↥D) ≃* ↥D := by
    rw [hStop]; exact Subgroup.topEquiv
  refine ⟨?_, ?_⟩
  · exact S.isPGroup'.of_equiv e
  · exact (MulEquiv.isCyclic e).1 hScyc

theorem sylow_le (h : KData X K z) (T : Sylow 2 X) :
    (T : Subgroup X) ≤ K ⊔ centralizer (K : Set X) := by
  have := h.normal
  exact sylow_le_sup_centralizer K h.facts.2.1 T.isPGroup'

theorem sup_isSylow' (h : KData X K z) (R : Sylow 2 ↥K) :
    IsPGroup 2 ↥((R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set X)) ∧
      ¬ 2 ∣ ((R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set X)).index := by
  have hKn := h.normal
  have hDn : (centralizer (K : Set X)).Normal := inferInstance
  obtain ⟨hDp, -⟩ := h.D_isPGroup_cyclic
  refine sup_isSylow (K := K) (D := centralizer (K : Set X)) (R := (R : Subgroup ↥K).map K.subtype)
    hDp h.inf_centralizer_eq_bot ?_ (R.isPGroup'.map K.subtype) (Subgroup.map_subtype_le _) ?_
    (fun T => h.sylow_le T)
  · rintro _ ⟨r, -, rfl⟩ d hd
    exact mem_centralizer_iff.1 hd r r.2
  · have : ((R : Subgroup ↥K).map K.subtype).relIndex K = (R : Subgroup ↥K).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        K.subtype_injective]
    rw [this]
    exact R.not_dvd_index

theorem R_facts (h : KData X K z) (R : Sylow 2 ↥K) :
    (∀ r ∈ (R : Subgroup ↥K).map K.subtype, ∀ r' ∈ (R : Subgroup ↥K).map K.subtype,
      r * r' = r' * r) ∧
    (∀ r ∈ (R : Subgroup ↥K).map K.subtype, r * r = 1) ∧
    Nat.card ↥((R : Subgroup ↥K).map K.subtype) = 8 := by
  obtain ⟨hRc, hRsq, hRcard, -⟩ := h.facts.2.2 R
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg (fun u : ↥(R : Subgroup ↥K) => ((u : ↥K) : X)) (hRc ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg (fun u : ↥(R : Subgroup ↥K) => ((u : ↥K) : X)) (hRsq ⟨a, ha⟩)
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hRcard

theorem S_comm (h : KData X K z) (R : Sylow 2 ↥K) {a b : X}
    (ha : a ∈ (R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set X))
    (hb : b ∈ (R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set X)) : a * b = b * a := by
  have hKn := h.normal
  have hDn : (centralizer (K : Set X)).Normal := inferInstance
  obtain ⟨-, hDc⟩ := h.D_isPGroup_cyclic
  obtain ⟨hRc, -, -⟩ := h.R_facts R
  obtain ⟨r₁, hr₁, d₁, hd₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
  obtain ⟨r₂, hr₂, d₂, hd₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
  have hRK : ∀ r ∈ (R : Subgroup ↥K).map K.subtype, r ∈ K := fun r hr => by
    obtain ⟨u, -, rfl⟩ := hr
    exact u.2
  have h12 : r₁ * r₂ = r₂ * r₁ := hRc r₁ hr₁ r₂ hr₂
  have hd12 : d₁ * d₂ = d₂ * d₁ := by
    have := congrArg Subtype.val (@mul_comm ↥(centralizer (K : Set X))
      (IsCyclic.commGroup (α := ↥(centralizer (K : Set X)))).toCommMagma ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩)
    simpa using this
  have hrd : ∀ r ∈ (R : Subgroup ↥K).map K.subtype, ∀ d ∈ centralizer (K : Set X),
      r * d = d * r := fun r hr d hd => mem_centralizer_iff.1 hd r (hRK r hr)
  calc r₁ * d₁ * (r₂ * d₂) = r₁ * (d₁ * r₂) * d₂ := by group
    _ = r₁ * (r₂ * d₁) * d₂ := by rw [← hrd r₂ hr₂ d₁ hd₁]
    _ = (r₁ * r₂) * (d₁ * d₂) := by group
    _ = (r₂ * r₁) * (d₂ * d₁) := by rw [h12, hd12]
    _ = r₂ * (r₁ * d₂) * d₁ := by group
    _ = r₂ * (d₂ * r₁) * d₁ := by rw [hrd r₁ hr₁ d₂ hd₂]
    _ = r₂ * d₂ * (r₁ * d₁) := by group

theorem exists_sq_in_D (h : KData X K z) (hD2 : Nat.card ↥(centralizer (K : Set X)) ≠ 2) :
    ∃ e ∈ centralizer (K : Set X), e * e = z := by
  obtain ⟨hDp, hDc⟩ := h.D_isPGroup_cyclic
  exact exists_sq_of_cyclic_two_group hDc hDp h.z_mem_centralizer h.ne h.sq hD2

theorem sq_eq_z (h : KData X K z) {R₀ : Subgroup X} (hR₀K : R₀ ≤ K)
    (hR₀sq : ∀ r ∈ R₀, r * r = 1) {s : X} (hs : s ∈ R₀ ⊔ centralizer (K : Set X))
    (hne : s * s ≠ 1) (hsq : (s * s) * (s * s) = 1) : s * s = z := by
  have hKn := h.normal
  have hDn : (centralizer (K : Set X)).Normal := inferInstance
  obtain ⟨-, hDc⟩ := h.D_isPGroup_cyclic
  obtain ⟨r, hr, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs
  have hcomm : r * d = d * r := mem_centralizer_iff.1 hd r (hR₀K hr)
  have hrr : r * r = 1 := hR₀sq r hr
  have hss : (r * d) * (r * d) = d * d := by
    calc (r * d) * (r * d) = r * (d * r) * d := by group
      _ = r * (r * d) * d := by rw [← hcomm]
      _ = (r * r) * (d * d) := by group
      _ = d * d := by rw [hrr, one_mul]
  rw [hss] at hne hsq ⊢
  exact eq_of_involutions_cyclic hDc (mul_mem hd hd) h.z_mem_centralizer hne h.ne hsq h.sq

end KData

end CFSG.GH74.Generic.S45
