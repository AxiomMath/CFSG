module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Reduce
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma313
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SuzTau
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup
open scoped commutatorElement

theorem index_ne_two_of_perfect {G : Type*} [Group G] [Group.IsPerfect G] (N : Subgroup G)
    [N.Normal] : N.index ≠ 2 := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := 2) h
  have hle := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
  rw [hle, index_top] at h
  norm_num at h

variable {Q : Type} [Group Q] [Finite Q]

theorem factorization_centralizer_quotient_add_le {x : Q} (hx : x * x = 1)
    (hZ : ∀ u ∈ center Q, ∀ v ∈ center Q, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v) :
    (Nat.card ↥(centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)))).factorization 2 +
        (Nat.card ↥(center Q)).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 + 1 := by
  classical
  set H := centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)) with hH
  obtain ⟨D, hD⟩ : ∃ D : Subgroup Q, D = H.comap (QuotientGroup.mk' (center Q)) := ⟨_, rfl⟩
  have hmemD : ∀ g : Q, g ∈ D ↔ (g : Q ⧸ center Q) * x = x * (g : Q ⧸ center Q) := by
    intro g
    rw [hD, mem_comap, hH, mem_centralizer_singleton_iff]
    rfl
  have hDc : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ center Q := fun g hg =>
    Walter.W67.MaxClass.commutator_mem_center ((hmemD g).mp hg)
  set φ := Walter.W67.MaxClass.commHom x D hDc with hφ
  have h1 := card_ker_mul_card_range φ
  have hcard : Nat.card D = Nat.card H * Nat.card (center Q) :=
    hD ▸ Walter.W67.MaxClass.card_comap_mk H
  have hker : Nat.card φ.ker = Nat.card ↥(centralizer ({x} : Set Q)) := by
    have hmap : φ.ker.map D.subtype = centralizer ({x} : Set Q) := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' : (g : Q) * x * (g : Q)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hg
        rw [mem_centralizer_singleton_iff]
        calc (g : Q) * x = (g : Q) * x * (g : Q)⁻¹ * x⁻¹ * (x * g) := by group
          _ = x * g := by rw [hg', one_mul]
      · intro hy
        have hyx := mem_centralizer_singleton_iff.mp hy
        have hyD : y ∈ D := by
          rw [hmemD]
          change ((y * x : Q) : Q ⧸ center Q) = ((x * y : Q) : Q ⧸ center Q)
          rw [hyx]
        refine ⟨⟨y, hyD⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        apply Subtype.ext
        change y * x * y⁻¹ * x⁻¹ = 1
        rw [hyx]
        group
    rw [← hmap, card_map_of_injective D.subtype_injective]
  have hsq : ∀ c ∈ φ.range, ((c : center Q) : Q) * c = 1 := by
    rintro c ⟨g, rfl⟩
    have hc : (g : Q) * x * (g : Q)⁻¹ * x⁻¹ ∈ center Q := hDc g g.2
    change ((g : Q) * x * (g : Q)⁻¹ * x⁻¹) * ((g : Q) * x * (g : Q)⁻¹ * x⁻¹) = 1
    set c' := (g : Q) * x * (g : Q)⁻¹ * x⁻¹ with hc'
    have e : (g : Q) * x * (g : Q)⁻¹ = c' * x := by rw [hc']; group
    have e2 : ((g : Q) * x * (g : Q)⁻¹) * ((g : Q) * x * (g : Q)⁻¹) = 1 := by
      calc ((g : Q) * x * (g : Q)⁻¹) * ((g : Q) * x * (g : Q)⁻¹) = (g : Q) * (x * x) * (g : Q)⁻¹ :=
            by group
        _ = 1 := by rw [hx]; group
    rw [e] at e2
    have hcx : x * c' = c' * x := mem_center_iff.mp hc x
    have e3 : (c' * x) * (c' * x) = c' * c' * (x * x) := by
      calc (c' * x) * (c' * x) = c' * (x * c') * x := by group
        _ = c' * (c' * x) * x := by rw [hcx]
        _ = c' * c' * (x * x) := by group
    rw [hx, mul_one] at e3
    rw [← e3]
    exact e2
  have hrange : Nat.card φ.range ≤ 2 := by
    have hinj : Function.Injective (fun c : φ.range => decide ((c : center Q) = 1)) := by
      intro c₁ c₂ h
      by_cases h₁ : (c₁ : center Q) = 1
      · have h₂ : (c₂ : center Q) = 1 := by simpa [h₁] using h
        exact Subtype.ext (h₁.trans h₂.symm)
      · have h₂ : (c₂ : center Q) ≠ 1 := by simpa [h₁] using h
        apply Subtype.ext
        apply Subtype.ext
        exact hZ _ (c₁ : center Q).2 _ (c₂ : center Q).2 (hsq _ c₁.2) (hsq _ c₂.2)
          (fun e => h₁ (Subtype.ext e)) (fun e => h₂ (Subtype.ext e))
    have h2 := Nat.card_le_card_of_injective _ hinj
    simpa using h2
  have hD' : Nat.card H * Nat.card ↥(center Q) =
      Nat.card ↥(centralizer ({x} : Set Q)) * Nat.card φ.range := by
    rw [← hcard, ← h1, hker]
  have hv := congrArg (fun n => n.factorization 2) hD'
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hv
  simp only [Finsupp.add_apply] at hv
  have hr : (Nat.card φ.range).factorization 2 ≤ 1 := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    interval_cases h : Nat.card φ.range
    · simp
    · simp [Nat.Prime.factorization_self Nat.prime_two]
  omega

theorem eq_one_or_eq_pow_half {P : Type*} [Group P] [Finite P] {p y : P} (hy : y ∈ zpowers p)
    (hy2 : y * y = 1) (hm : 2 ∣ orderOf p) : y = 1 ∨ y = p ^ (orderOf p / 2) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p ^ n = y := mem_powers_iff_mem_zpowers.mpr hy
  have hm0 : 0 < orderOf p := orderOf_pos p
  rw [← pow_mod_orderOf] at hy2 ⊢
  set k := n % orderOf p with hk
  have hklt : k < orderOf p := Nat.mod_lt _ hm0
  have hdvd : orderOf p ∣ 2 * k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [two_mul, pow_add]
    exact hy2
  obtain ⟨j, hj⟩ := hdvd
  have hj2 : j < 2 := by
    by_contra hge
    push Not at hge
    have : orderOf p * 2 ≤ orderOf p * j := Nat.mul_le_mul_left _ hge
    omega
  interval_cases j
  · left
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero]
  · right
    obtain ⟨m', hm'⟩ := hm
    congr 1
    omega

theorem eight_le_of_card_inf_centralizer_eq_four {S : Type} [Group S] [Finite S]
    [Group.IsPerfect S] {s : S} (hs : orderOf s = 2) {T : Sylow 2 S} (hsT : s ∈ (T : Subgroup S))
    (hTC : Nat.card ↥((T : Subgroup S) ⊓ centralizer ({s} : Set S)) = 4)
    (h8 : 8 ≤ Nat.card ↥(T : Subgroup S)) :
    3 ≤ (Nat.card ↥(centralizer ({s} : Set S))).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b : ↥(T : Subgroup S) := ⟨s, hsT⟩ with hb
  have hb2 : orderOf b = 2 := by rw [hb, Subgroup.orderOf_mk]; exact hs
  have hcb : Nat.card ↥(centralizer ({b} : Set ↥(T : Subgroup S))) = 4 := by
    have hmap : (centralizer ({b} : Set ↥(T : Subgroup S))).map (T : Subgroup S).subtype =
        (T : Subgroup S) ⊓ centralizer ({s} : Set S) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine mem_inf.mpr ⟨t.2, mem_centralizer_singleton_iff.mpr ?_⟩
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp ht)
      · intro hy
        obtain ⟨hyT, hys⟩ := mem_inf.mp hy
        refine ⟨⟨y, hyT⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
        exact Subtype.ext (mem_centralizer_singleton_iff.mp hys)
    rw [← hTC, ← hmap, card_map_of_injective (Subgroup.subtype_injective _)]
  obtain ⟨p, r, hcl, hp, hr, hrel⟩ :=
    GSThmB.suzukiTausskyInput ↥(T : Subgroup S) T.isPGroup' h8 b hb2 hcb
  set m := orderOf p with hmdef
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hm4 : 4 ∣ m := by
    have hme : m ∣ 2 ^ e := he ▸ Dvd.intro_left 2 hp
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hme
    have h2i : 8 ≤ 2 * 2 ^ i := by rw [← hi]; omega
    have hi2 : 2 ≤ i := by
      by_contra hlt
      push Not at hlt
      interval_cases i <;> norm_num at h2i
    rw [hi]
    exact (by norm_num : (4 : ℕ) ∣ 2 ^ 2).trans (pow_dvd_pow 2 hi2)
  obtain ⟨t, ht⟩ := hm4
  have hm2 : 2 ∣ m := ⟨2 * t, by omega⟩
  set z := p ^ (m / 2) with hzdef
  have hpm : p ^ m = 1 := pow_orderOf_eq_one p
  have hzc : ∀ y : ↥(T : Subgroup S), y * z = z * y := by
    have hcen : (⊤ : Subgroup ↥(T : Subgroup S)) ≤ centralizer ({z} : Set ↥(T : Subgroup S)) := by
      rw [← hcl, closure_le]
      intro w hw
      rcases hw with rfl | hw
      · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, hzdef]
        exact (Commute.pow_right (Commute.refl w) _).eq
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        have hconj : w * z * w⁻¹ = z := by
          rw [hzdef, ← conj_pow]
          rcases hrel with h | h
          · rw [h, inv_pow]
            have hz2 : p ^ (m / 2) * p ^ (m / 2) = 1 := by
              rw [← pow_add, show m / 2 + m / 2 = m by omega, hpm]
            exact inv_eq_of_mul_eq_one_left hz2
          · rw [h, ← pow_mul]
            have hexp : (m / 2 - 1) * (m / 2) = m * (t - 1) + m / 2 := by
              have hp0 := orderOf_pos p
              have ht1 : 1 ≤ t := by omega
              obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
              rw [ht, show 4 * (u + 1) / 2 = 2 * u + 2 by omega,
                show 2 * u + 2 - 1 = 2 * u + 1 by omega, show u + 1 - 1 = u by omega]
              ring
            rw [hexp, pow_add, pow_mul, hpm, one_pow, one_mul]
        calc w * z = w * z * w⁻¹ * w := by group
          _ = z * w := by rw [hconj]
    intro y
    exact (mem_centralizer_singleton_iff.mp (hcen (mem_top y)))
  set U : Subgroup S := (zpowers p).map (T : Subgroup S).subtype with hU
  have hUT : U ≤ (T : Subgroup S) := map_subtype_le _
  have hUcard : Nat.card U = m := by
    rw [hU, card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers]
  have hUidx : U.relIndex (T : Subgroup S) = 2 := by
    have h := relIndex_mul_card U (T : Subgroup S)
    rw [inf_of_le_left hUT, hUcard, ← hp] at h
    exact Nat.eq_of_mul_eq_mul_right (orderOf_pos p) h
  have hsU : s ∉ U := by
    rintro ⟨y, hy, hys⟩
    have hyb : y = b := Subtype.ext hys
    have hy2 : y * y = 1 := by
      rw [hyb]; apply Subtype.ext
      change s * s = 1
      rw [← pow_two, ← hs, pow_orderOf_eq_one]
    rcases eq_one_or_eq_pow_half hy hy2 hm2 with h1 | hz
    · rw [hyb] at h1
      have : s = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at hs
      norm_num at hs
    ·
      have hyz : y = z := hz.trans (by rw [hzdef, hmdef])
      have hTs : (T : Subgroup S) ⊓ centralizer ({s} : Set S) = (T : Subgroup S) := by
        refine inf_eq_left.mpr fun w hw => mem_centralizer_singleton_iff.mpr ?_
        have h := hzc ⟨w, hw⟩
        rw [← hyz, hyb] at h
        exact congrArg Subtype.val h
      rw [hTs] at hTC
      omega
  have hconjU : ∃ g : S, g⁻¹ * s * g ∈ U := by
    by_contra hno
    push Not at hno
    obtain ⟨N, hN, hNidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson T.isPGroup'
      T.not_dvd_index hUT hUidx hsT hsU (fun y hyT hyU => by
        rw [hs]
        have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
        have hpos : 0 < orderOf y := orderOf_pos y
        have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
        omega) hno
    exact index_ne_two_of_perfect N hNidx
  obtain ⟨g, hg⟩ := hconjU
  obtain ⟨y, hy, hyg⟩ := hg
  have hyg' : (y : S) = g⁻¹ * s * g := hyg
  have hy2 : y * y = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hyg', OneMemClass.coe_one]
    calc g⁻¹ * s * g * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
      _ = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]; group
  have hyz : y = z := by
    rcases eq_one_or_eq_pow_half hy hy2 hm2 with h1 | hz
    · exfalso
      have : g⁻¹ * s * g = 1 := by rw [← hyg', h1, OneMemClass.coe_one]
      have hs1 : s = 1 := by
        calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
          _ = 1 := by rw [this]; group
      rw [hs1, orderOf_one] at hs
      norm_num at hs
    · exact hz.trans (by rw [hzdef, hmdef])
  have hcardC : Nat.card ↥(centralizer ({s} : Set S)) =
      Nat.card ↥(centralizer ({((z : ↥(T : Subgroup S)) : S)} : Set S)) := by
    have hmap : (centralizer ({s} : Set S)).map (MulAut.conj g⁻¹).toMonoidHom =
        centralizer ({((z : ↥(T : Subgroup S)) : S)} : Set S) := by
      rw [← hyz, hyg']
      ext w
      simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩
        calc g⁻¹ * v * g * (g⁻¹ * s * g) = g⁻¹ * (v * s) * g := by group
          _ = g⁻¹ * (s * v) * g := by rw [hv]
          _ = g⁻¹ * s * g * (g⁻¹ * v * g) := by group
      · intro hw
        refine ⟨g * w * g⁻¹, ?_, by group⟩
        calc g * w * g⁻¹ * s = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * s * g * w) * g⁻¹ := by rw [hw]
          _ = s * (g * w * g⁻¹) := by group
    rw [← hmap, card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hTz : (T : Subgroup S) ≤ centralizer ({((z : ↥(T : Subgroup S)) : S)} : Set S) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hzc ⟨w, hw⟩)
  have hdvd := card_dvd_of_le hTz
  rw [← hcardC, he] at hdvd
  have he3 : 3 ≤ e := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [he] at h8
    omega
  exact he3.trans ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd)

omit [Finite Q] in
theorem mem_sylow_of_mk_mem {T : Sylow 2 Q} {y : Q} (hy : ∃ k : ℕ, orderOf y = 2 ^ k)
    (hyT : (y : Q ⧸ center Q) ∈ (T : Subgroup Q).map (QuotientGroup.mk' (center Q))) :
    y ∈ (T : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, hty⟩ := hyT
  have hw : t⁻¹ * y ∈ center Q := QuotientGroup.eq.mp hty
  set w := t⁻¹ * y with hwdef
  obtain ⟨k, hk⟩ := hy
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨t, htT⟩
  have ht : t ^ (2 ^ e) = 1 := by
    have h := pow_orderOf_eq_one (⟨t, htT⟩ : ↥(T : Subgroup Q))
    rw [he] at h
    exact congrArg Subtype.val h
  have hyk : y ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have hyN : y ^ (2 ^ (k + e)) = 1 := by rw [pow_add, pow_mul, hyk, one_pow]
  have htN : t ^ (2 ^ (k + e)) = 1 := by rw [pow_add, mul_comm, pow_mul, ht, one_pow]
  have hcomm : Commute t w := mem_center_iff.mp hw t
  have hwN : w ^ (2 ^ (k + e)) = 1 := by
    have hyt : y = t * w := by rw [hwdef]; group
    have h := hcomm.mul_pow (2 ^ (k + e))
    rw [← hyt, hyN, htN, one_mul] at h
    exact h.symm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwN)
  have hp : IsPGroup 2 (zpowers w) := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have : (zpowers w).Normal := normal_of_le_center (zpowers_le.mpr hw)
  have hwT : w ∈ (T : Subgroup Q) := hp.le_sylow_of_normal T (mem_zpowers w)
  have hyt : y = t * w := by rw [hwdef]; group
  rw [hyt]
  exact mul_mem htT hwT

theorem eq_or_eq_of_card_eq_four {G : Type*} [Group G] {W : Subgroup G} [Finite W]
    (hW : Nat.card W = 4) {a b : G} (ha : a ∈ W) (hb : b ∈ W) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hexp : ∀ t ∈ W, t * t = 1) {c : G} (hc : c ∈ W) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hca, hcb, hcab⟩ := hne
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have hb' : b * b = 1 := hexp b hb
    calc a = a * b * b := by rw [mul_assoc, hb', mul_one]
      _ = b := by rw [h, one_mul]
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hsub : ({1, a, b, a * b, c} : Set G) ⊆ (W : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact ha
    · exact hb
    · exact mul_mem ha hb
    · exact hc
  have hcard : ({1, a, b, a * b, c} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hcab.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨habb.symm, hcb.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, haba.symm, hca.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm, hc1.symm⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hW] at hle
  omega

theorem commutator_mem_zpowers_of_four {G : Type*} [Group G] {a b k : G}
    (hk : a * b * a⁻¹ * b⁻¹ = k) (hkc : ∀ g : G, g * k = k * g) {w w' : G}
    (hw : w = 1 ∨ w = a ∨ w = b ∨ w = a * b) (hw' : w' = 1 ∨ w' = a ∨ w' = b ∨ w' = a * b) :
    w * w' * w⁻¹ * w'⁻¹ ∈ zpowers k := by
  have hab : a * (a * b) * a⁻¹ * (a * b)⁻¹ = k := by
    calc a * (a * b) * a⁻¹ * (a * b)⁻¹ = a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ := by group
      _ = k := by rw [hk, hkc a, mul_inv_cancel_right]
  have hbab : b * (a * b) * b⁻¹ * (a * b)⁻¹ = k⁻¹ := by
    rw [← hk]
    group
  have hba : b * a * b⁻¹ * a⁻¹ = k⁻¹ := by
    rw [← hk]
    group
  have habinv : ∀ u v : G, u * v * u⁻¹ * v⁻¹ = (v * u * v⁻¹ * u⁻¹)⁻¹ := fun u v => by group
  rcases hw with rfl | rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl | rfl <;>
    first
    | (convert one_mem (zpowers k) using 1; all_goals group; done)
    | (rw [hk]; exact mem_zpowers k)
    | (rw [hab]; exact mem_zpowers k)
    | (rw [hba]; exact inv_mem (mem_zpowers k))
    | (rw [hbab]; exact inv_mem (mem_zpowers k))
    | (rw [habinv, hab]; exact inv_mem (mem_zpowers k))
    | (rw [habinv, hbab, inv_inv]; exact mem_zpowers k)

theorem false_of_sylow_card_four [Group.IsPerfect Q] (hZ2 : 2 ∣ Nat.card ↥(center Q)) {x : Q}
    (hx : orderOf x = 2) (hxZ : x ∉ center Q)
    (h4 : ∀ T : Sylow 2 (Q ⧸ center Q), Nat.card ↥(T : Subgroup (Q ⧸ center Q)) = 4) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hx2 : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hxT'⟩ := hx2.exists_le_sylow
  have hxT : x ∈ (T : Subgroup Q) := hxT' (mem_zpowers x)
  set T' : Sylow 2 (Q ⧸ center Q) := T.mapSurjective hπs with hT'
  set W : Subgroup (Q ⧸ center Q) := (T' : Subgroup (Q ⧸ center Q)) with hW
  have hWeq : W = (T : Subgroup Q).map π := rfl
  have hW4 : Nat.card W = 4 := h4 T'
  set xb := π x with hxb
  have hxW : xb ∈ W := by rw [hWeq]; exact mem_map_of_mem _ hxT
  have hx1 : xb ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
  have hWnc : ¬ IsCyclic W := by
    intro hc
    have := Fintype.ofFinite (Q ⧸ center Q)
    have heven : Even (Fintype.card (Q ⧸ center Q)) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mpr ((show 2 ∣ 4 by norm_num).trans (hW4 ▸ card_subgroup_dvd_card W))
    obtain ⟨-, -, hn, hidx⟩ := LinearGroups.cyclic_sylow_index_two heven T' hc
    exact index_ne_two_of_perfect _ hidx
  have hexp : ∀ t ∈ W, t * t = 1 := by
    intro t ht
    have hdvd : orderOf t ∣ 2 ^ 2 := by
      have h := orderOf_dvd_natCard (⟨t, ht⟩ : W)
      rw [Subgroup.orderOf_mk, hW4] at h
      simpa using h
    obtain ⟨i, hi, hti⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hi2 : i ≠ 2 := by
      rintro rfl
      exact hWnc (isCyclic_of_orderOf_eq_card (⟨t, ht⟩ : W)
        (by rw [Subgroup.orderOf_mk, hti, hW4]; norm_num))
    have h2 : orderOf t ∣ 2 := by
      rw [hti]
      exact (pow_dvd_pow 2 (show i ≤ 1 by omega)).trans (by norm_num)
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hcomm : ∀ s ∈ W, ∀ t ∈ W, s * t = t * s := by
    intro s hs t ht
    rw [eq_inv_of_mul_eq_one_left (hexp _ (mul_mem hs ht)), mul_inv_rev,
      inv_eq_of_mul_eq_one_left (hexp t ht), inv_eq_of_mul_eq_one_left (hexp s hs)]
  have hfour := fun {a b : Q ⧸ center Q} (ha : a ∈ W) (hb : b ∈ W) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) {c : Q ⧸ center Q} (hc : c ∈ W) =>
    eq_or_eq_of_card_eq_four hW4 ha hb ha1 hb1 hab hexp hc
  have hNC : ¬ normalizer (W : Set (Q ⧸ center Q)) ≤ centralizer (W : Set (Q ⧸ center Q)) := by
    intro hP
    have : IsMulCommutative ↥T' := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hcomp := MonoidHom.ker_transferSylow_isComplement' T' hP
    have hker := Abelianization.commutator_subset_ker (MonoidHom.transferSylow T' hP)
    rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hker
    have hcm := hcomp.card_mul_card
    rw [hker, card_top] at hcm
    have hcm' : Nat.card (Q ⧸ center Q) * 4 = Nat.card (Q ⧸ center Q) := by
      rw [← hW4]
      exact hcm
    have hpos : 0 < Nat.card (Q ⧸ center Q) := Nat.card_pos
    omega
  obtain ⟨g, hgN, hgC⟩ : ∃ g, g ∈ normalizer (W : Set (Q ⧸ center Q)) ∧
      g ∉ centralizer (W : Set (Q ⧸ center Q)) := by
    by_contra hno
    push Not at hno
    exact hNC hno
  have hgW : ∀ h ∈ normalizer (W : Set (Q ⧸ center Q)), ∀ t ∈ W, h * t * h⁻¹ ∈ W :=
    fun h hh t ht => (mem_normalizer_iff.mp hh t).mp ht
  obtain ⟨i, m, hm, hgo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  have hgmC : g ^ m ∈ centralizer (W : Set (Q ⧸ center Q)) := by
    have hord : orderOf (g ^ m) = 2 ^ i := by
      rw [orderOf_pow_of_dvd hm0 ⟨2 ^ i, by rw [hgo, mul_comm]⟩, hgo,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    have hzp : IsPGroup 2 (zpowers (g ^ m)) :=
      IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hord])
    have hsup := IsPGroup.to_sup_of_normal_left' T'.isPGroup' hzp (zpowers_le.mpr (pow_mem hgN m))
    have heq := T'.is_maximal' hsup le_sup_left
    have hgmW : g ^ m ∈ W := by
      have h : g ^ m ∈ (T' : Subgroup (Q ⧸ center Q)) ⊔ zpowers (g ^ m) :=
        mem_sup_right (mem_zpowers (g ^ m))
      rwa [heq] at h
    rw [mem_centralizer_iff]
    intro t ht
    exact hcomm t ht _ hgmW
  obtain ⟨j, hj⟩ := hm
  have hfpf : ∀ h ∈ normalizer (W : Set (Q ⧸ center Q)), h ∉ centralizer (W : Set (Q ⧸ center Q)) →
      h ^ m ∈ centralizer (W : Set (Q ⧸ center Q)) → ∀ t ∈ W, t ≠ 1 → h * t * h⁻¹ ≠ t := by
    intro h hhN hhC hhm t ht ht1 hfix
    apply hhC
    have hh2 : h ^ 2 ∈ centralizer (W : Set (Q ⧸ center Q)) := by
      rw [mem_centralizer_iff]
      intro y hy
      suffices hconj : h ^ 2 * y * (h ^ 2)⁻¹ = y by
        calc y * h ^ 2 = h ^ 2 * y * (h ^ 2)⁻¹ * h ^ 2 := by rw [hconj]
          _ = h ^ 2 * y := by group
      have hyW' := hgW h hhN y hy
      by_cases hy1 : y = 1
      · rw [hy1]; group
      by_cases hyt : y = t
      · rw [hyt, pow_two, mul_inv_rev,
          show h * h * t * (h⁻¹ * h⁻¹) = h * (h * t * h⁻¹) * h⁻¹ by group, hfix, hfix]
      have hy'1 : h * y * h⁻¹ ≠ 1 := fun e => hy1 (by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = 1 := by rw [e]; group)
      have hy't : h * y * h⁻¹ ≠ t := fun e => hyt (by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = h⁻¹ * (h * t * h⁻¹) * h := by rw [e, hfix]
          _ = t := by group)
      rcases hfour ht hy ht1 hy1 (Ne.symm hyt) hyW' with e | e | e | e
      · exact absurd e hy'1
      · exact absurd e hy't
      · rw [pow_two, mul_inv_rev, show h * h * y * (h⁻¹ * h⁻¹) = h * (h * y * h⁻¹) * h⁻¹ by group,
          e, e]
      · have e2 : h * (t * y) * h⁻¹ = y := by
          rw [show h * (t * y) * h⁻¹ = (h * t * h⁻¹) * (h * y * h⁻¹) by group, hfix, e,
            ← mul_assoc, hexp t ht, one_mul]
        rw [pow_two, mul_inv_rev, show h * h * y * (h⁻¹ * h⁻¹) = h * (h * y * h⁻¹) * h⁻¹ by group,
          e, e2]
    have e : h ^ m = h * (h ^ 2) ^ j := by rw [hj, pow_succ', ← pow_mul]
    have he : h = h ^ m * ((h ^ 2) ^ j)⁻¹ := by rw [e, mul_inv_cancel_right]
    rw [he]
    exact mul_mem hhm (inv_mem (pow_mem hh2 j))
  set bb := g * xb * g⁻¹ with hbb
  set cb := g * bb * g⁻¹ with hcb
  have hbbW : bb ∈ W := hgW g hgN xb hxW
  have hcbW : cb ∈ W := hgW g hgN bb hbbW
  have hbb1 : bb ≠ 1 := fun e => hx1 (by
    calc xb = g⁻¹ * (g * xb * g⁻¹) * g := by group
      _ = 1 := by rw [← hbb, e]; group)
  have hcb1 : cb ≠ 1 := fun e => hbb1 (by
    calc bb = g⁻¹ * (g * bb * g⁻¹) * g := by group
      _ = 1 := by rw [← hcb, e]; group)
  have hbx : bb ≠ xb := hfpf g hgN hgC hgmC xb hxW hx1
  have hcbb : cb ≠ bb := hfpf g hgN hgC hgmC bb hbbW hbb1
  have hcx : cb ≠ xb := by
    have hg2C : g ^ 2 ∉ centralizer (W : Set (Q ⧸ center Q)) := by
      intro h2
      apply hgC
      have e : g ^ m = g * (g ^ 2) ^ j := by rw [hj, pow_succ', ← pow_mul]
      have he : g = g ^ m * ((g ^ 2) ^ j)⁻¹ := by rw [e, mul_inv_cancel_right]
      rw [he]
      exact mul_mem hgmC (inv_mem (pow_mem h2 j))
    have hg2m : (g ^ 2) ^ m ∈ centralizer (W : Set (Q ⧸ center Q)) := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_mem hgmC 2
    intro e
    apply hfpf (g ^ 2) (pow_mem hgN 2) hg2C hg2m xb hxW hx1
    rw [show g ^ 2 * xb * (g ^ 2)⁻¹ = cb by
      rw [hcb, hbb, pow_two, mul_inv_rev]; simp only [mul_assoc], e]
  have hcbeq : cb = xb * bb := by
    rcases hfour hxW hbbW hx1 hbb1 (Ne.symm hbx) hcbW with e | e | e | e
    · exact absurd e hcb1
    · exact absurd e hcx
    · exact absurd e hcbb
    · exact e
  obtain ⟨gh, hgh⟩ := hπs g
  set b := gh * x * gh⁻¹ with hbdef
  set c := gh * b * gh⁻¹ with hcdef
  have hπb : π b = bb := by rw [hbdef, hbb, hxb, map_mul, map_mul, map_inv, hgh]
  have hπc : π c = cb := by rw [hcdef, hcb, map_mul, map_mul, map_inv, hgh, hπb]
  have hb2 : orderOf b = 2 := by
    rw [hbdef, show gh * x * gh⁻¹ = (MulAut.conj gh) x by simp, MulEquiv.orderOf_eq, hx]
  have hc2 : orderOf c = 2 := by
    rw [hcdef, show gh * b * gh⁻¹ = (MulAut.conj gh) b by simp, MulEquiv.orderOf_eq, hb2]
  have hbT : b ∈ (T : Subgroup Q) :=
    mem_sylow_of_mk_mem ⟨1, by rw [hb2, pow_one]⟩
      (by rw [← hWeq]; change π b ∈ W; rw [hπb]; exact hbbW)
  have hcT : c ∈ (T : Subgroup Q) :=
    mem_sylow_of_mk_mem ⟨1, by rw [hc2, pow_one]⟩
      (by rw [← hWeq]; change π c ∈ W; rw [hπc]; exact hcbW)
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  set z₁ := c⁻¹ * (x * b) with hz₁
  have hz₁Z : z₁ ∈ center Q := by
    rw [← QuotientGroup.eq_one_iff]
    change π z₁ = 1
    rw [hz₁, map_mul, map_mul, map_inv, hπc, hπb, hcbeq, ← hxb]
    group
  have hz₁T : z₁ ∈ (T : Subgroup Q) := mul_mem (inv_mem hcT) (mul_mem hxT hbT)
  have hz₁c : ∀ g' : Q, g' * z₁ = z₁ * g' := fun g' => mem_center_iff.mp hz₁Z g'
  have hk : x * b * x⁻¹ * b⁻¹ = z₁ * z₁ := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
    have hbb' : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hbb'
    have hab : x * b = c * z₁ := by rw [hz₁]; group
    rw [hxi, hbi]
    calc x * b * x * b = (x * b) * (x * b) := by group
      _ = c * z₁ * (c * z₁) := by rw [hab]
      _ = c * (z₁ * c) * z₁ := by group
      _ = c * (c * z₁) * z₁ := by rw [hz₁c c]
      _ = c * c * (z₁ * z₁) := by group
      _ = z₁ * z₁ := by rw [hcc, one_mul]
  have hkc : ∀ g' : Q, g' * (z₁ * z₁) = (z₁ * z₁) * g' := fun g' =>
    mem_center_iff.mp (mul_mem hz₁Z hz₁Z) g'
  have hdec : ∀ y ∈ (T : Subgroup Q), ∃ w : Q, (w = 1 ∨ w = x ∨ w = b ∨ w = x * b) ∧
      w⁻¹ * y ∈ center Q := by
    intro y hy
    have hyW : π y ∈ W := by rw [hWeq]; exact mem_map_of_mem _ hy
    rcases hfour hxW hbbW hx1 hbb1 (Ne.symm hbx) hyW with e | e | e | e
    · exact ⟨1, Or.inl rfl, by rw [inv_one, one_mul]; exact (QuotientGroup.eq_one_iff y).mp e⟩
    · exact ⟨x, Or.inr (Or.inl rfl), QuotientGroup.eq.mp e.symm⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), QuotientGroup.eq.mp (hπb.trans e.symm)⟩
    · refine ⟨x * b, Or.inr (Or.inr (Or.inr rfl)), QuotientGroup.eq.mp ?_⟩
      change π (x * b) = π y
      rw [map_mul, hπb, e, hxb]
  have hcommle : ⁅(T : Subgroup Q), (T : Subgroup Q)⁆ ≤ zpowers (z₁ * z₁) := by
    rw [commutator_le]
    intro y hy y' hy'
    obtain ⟨w, hw, hwz⟩ := hdec y hy
    obtain ⟨w', hw', hwz'⟩ := hdec y' hy'
    have e1 : y = w * (w⁻¹ * y) := by group
    have e2 : y' = w' * (w'⁻¹ * y') := by group
    rw [e1, e2, commutatorElement_def, Sol76.commutator_mul_mul_eq
      (mem_center_iff.mp hwz w').symm
      (mem_center_iff.mp hwz' _)
      (mem_center_iff.mp hwz' w⁻¹).symm]
    exact commutator_mem_zpowers_of_four hk hkc hw hw'
  have hZle : ∀ z ∈ (T : Subgroup Q), z ∈ center Q → z ∈ zpowers (z₁ * z₁) := by
    intro z hzT hzZ
    have key : ∀ (k₀ : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k₀ * g₀ ∈ (T : Subgroup Q) →
        g₀⁻¹ * z ^ k₀ * g₀ = z ^ k₀ := by
      intro k₀ g₀ _
      have hzk : z ^ k₀ ∈ center Q := pow_mem hzZ k₀
      rw [mul_assoc, ← mem_center_iff.mp hzk g₀]
      group
    have htr := MonoidHom.transfer_eq_pow
      (Abelianization.of : ↥(T : Subgroup Q) →* Abelianization ↥(T : Subgroup Q)) z key
    have h1 : MonoidHom.transfer
        (Abelianization.of : ↥(T : Subgroup Q) →* Abelianization ↥(T : Subgroup Q)) z = 1 := by
      have hle := Abelianization.commutator_subset_ker (MonoidHom.transfer
        (Abelianization.of : ↥(T : Subgroup Q) →* Abelianization ↥(T : Subgroup Q)))
      rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
      have hz : z ∈ (MonoidHom.transfer
          (Abelianization.of : ↥(T : Subgroup Q) →* Abelianization ↥(T : Subgroup Q))).ker := by
        rw [hle]; trivial
      exact MonoidHom.mem_ker.mp hz
    rw [htr] at h1
    have h2 := MonoidHom.mem_ker.mpr h1
    rw [Abelianization.ker_of] at h2
    have h3 : z ^ (T : Subgroup Q).index ∈ ⁅(T : Subgroup Q), (T : Subgroup Q)⁆ := by
      rw [← map_subtype_commutator]
      exact ⟨_, h2, rfl⟩
    have h4 := hcommle h3
    obtain ⟨e', he'⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨z, hzT⟩
    rw [Subgroup.orderOf_mk] at he'
    have hcop : Nat.Coprime (T : Subgroup Q).index (orderOf z) := by
      rw [he']
      exact Nat.Coprime.pow_right e' (Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr T.not_dvd_index))
    obtain ⟨n', hn'⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hn']
    exact pow_mem h4 n'
  have hz₁1 : z₁ = 1 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hZle z₁ hz₁T hz₁Z)
    obtain ⟨e', he'⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨z₁, hz₁T⟩
    rw [Subgroup.orderOf_mk] at he'
    have h' : z₁ ^ (2 * n - 1) = 1 := by
      rw [zpow_sub_one, zpow_mul, zpow_two, hn, mul_inv_cancel]
    have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr h'
    rw [he'] at hdvd
    rcases e' with _ | e'
    · rw [pow_zero] at he'
      exact orderOf_eq_one_iff.mp he'
    · exfalso
      have h2 : (2 : ℤ) ∣ 2 * n - 1 := by
        refine Dvd.dvd.trans ?_ hdvd
        push_cast
        exact dvd_pow_self 2 (Nat.succ_ne_zero e')
      omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center Q)) 2 hZ2
  have huT : (u : Q) ∈ (T : Subgroup Q) := by
    have : (zpowers (u : Q)).Normal := normal_of_le_center (zpowers_le.mpr u.2)
    have hp : IsPGroup 2 (zpowers (u : Q)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hu, pow_one])
    exact hp.le_sylow_of_normal T (mem_zpowers _)
  have hu1 := hZle u huT u.2
  rw [hz₁1, mul_one, zpowers_one_eq_bot, mem_bot] at hu1
  have : u = 1 := Subtype.ext hu1
  rw [this, orderOf_one] at hu
  norm_num at hu

theorem two_add_factorization_le_of_center (hQ : IsQuasisimple Q)
    (hZ : ∀ u ∈ center Q, ∀ v ∈ center Q, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v)
    {x : Q} (hx : orderOf x = 2) (hxZ : x ∉ center Q) :
    (Nat.card ↥(center Q)).factorization 2 + 2 ≤
      (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 := by
  classical
  have : Group.IsPerfect Q := hQ.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  by_cases h2 : 2 ∣ Nat.card ↥(center Q)
  · have hA := factorization_centralizer_quotient_add_le hxx hZ
    suffices hB : 3 ≤ (Nat.card ↥(centralizer
        ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)))).factorization 2 by omega
    set xb : Q ⧸ center Q := (x : Q ⧸ center Q) with hxb
    have hx1 : xb ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
    have hxb2 : orderOf xb = 2 := by
      refine orderOf_eq_prime ?_ hx1
      rw [hxb, ← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h4 : 2 ≤ (Nat.card ↥(centralizer ({xb} : Set (Q ⧸ center Q)))).factorization 2 := by
      have h := four_dvd_card_centralizer_of_perfect hxb2
      exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h)
    by_contra hlt
    push Not at hlt
    have hv2 : (Nat.card ↥(centralizer ({xb} : Set (Q ⧸ center Q)))).factorization 2 = 2 := by omega
    set C := centralizer ({xb} : Set (Q ⧸ center Q)) with hC
    have hxC : xb ∈ C := mem_centralizer_singleton_iff.mpr rfl
    have hxz : IsPGroup 2 (zpowers (⟨xb, hxC⟩ : C)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hxb2, pow_one])
    obtain ⟨R, hR⟩ := hxz.exists_le_sylow
    have hRp : IsPGroup 2 ((R : Subgroup C).map C.subtype) := R.isPGroup'.map _
    obtain ⟨T, hT⟩ := hRp.exists_le_sylow
    have hRcard : Nat.card ↥((R : Subgroup C).map C.subtype) = 4 := by
      rw [card_map_of_injective (Subgroup.subtype_injective _), R.card_eq_multiplicity, hv2]
      norm_num
    have hxT : xb ∈ (T : Subgroup (Q ⧸ center Q)) := hT ⟨⟨xb, hxC⟩, hR (mem_zpowers _), rfl⟩
    have hTC : Nat.card ↥((T : Subgroup (Q ⧸ center Q)) ⊓ C) = 4 := by
      apply le_antisymm
      · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
          (T.isPGroup'.to_le (inf_le_left : (T : Subgroup (Q ⧸ center Q)) ⊓ C ≤ T))
        have hdvd : 2 ^ k ∣ Nat.card C := hk ▸ card_dvd_of_le inf_le_right
        have hk2 : k ≤ 2 :=
          ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd).trans hv2.le
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
          _ = 4 := by norm_num
      · rw [← hRcard]
        exact card_le_of_le (le_inf hT (map_subtype_le _))
    by_cases h8 : 8 ≤ Nat.card ↥(T : Subgroup (Q ⧸ center Q))
    · have := eight_le_of_card_inf_centralizer_eq_four hxb2 hxT hTC h8
      rw [← hC] at this
      omega
    ·
      have hT4 : Nat.card ↥(T : Subgroup (Q ⧸ center Q)) = 4 := by
        have hle : 4 ≤ Nat.card ↥(T : Subgroup (Q ⧸ center Q)) := hTC ▸ card_le_of_le inf_le_left
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
        rw [hk] at hle h8 ⊢
        have hk2 : k = 2 := by
          rcases Nat.lt_or_ge k 3 with hlt | hge
          · interval_cases k <;> first | rfl | (norm_num at hle)
          · exfalso
            have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
            omega
        rw [hk2]
        norm_num
      refine false_of_sylow_card_four h2 hx hxZ fun T'' => ?_
      rw [T''.card_eq_multiplicity, ← T.card_eq_multiplicity, hT4]
  · have h0 : (Nat.card ↥(center Q)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd h2
    have h4 := four_dvd_card_centralizer_of_perfect hx
    have h5 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
      (show 2 ^ 2 ∣ Nat.card ↥(centralizer ({x} : Set Q)) by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4)
    omega

@[expose] def QuasisimpleCentralFourInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Blueprint.Catalog (Q ⧸ center Q) →
    ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u ≠ v → u ∈ center Q → v ∈ center Q →
      (∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
      ∀ x : Q, orderOf x = 2 → x ∉ center Q →
        (Nat.card ↥(center Q)).factorization 2 + 2 ≤
          (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2

theorem quasisimpleTwoPartInput_of_centralFour (h : QuasisimpleCentralFourInput) :
    QuasisimpleTwoPartInput := by
  refine ⟨fun Q _ _ hQ hcat u v hu hv huv huZ hvZ =>
      (h Q hQ hcat u v hu hv huv huZ hvZ).1, fun Q _ _ hQ hcat x hx hxZ => ?_⟩
  by_cases hZ : ∀ u ∈ center Q, ∀ v ∈ center Q, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v
  · exact two_add_factorization_le_of_center hQ hZ hx hxZ
  · push Not at hZ
    obtain ⟨u, hu, v, hv, hu2, hv2, hu1, hv1, huv⟩ := hZ
    have hu' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    have hv' : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1
    exact (h Q hQ hcat u v hu' hv' huv hu hv).2 x hx hxZ

end CFSG.ComponentClassification.Sol76T13
