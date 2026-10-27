module

public import CFSG.ClassicalInvolution.Q3.TL3T3

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_closure_of_comm {T : Set G} (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (h2 : ∀ x ∈ T, ∃ k : ℕ, x ^ 2 ^ k = 1) : IsPGroup 2 ↥(Subgroup.closure T) := by
  have hc : ∀ x ∈ Subgroup.closure T, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
    intro x hx y hy
    have hpair : T.Pairwise Commute := fun a ha b hb _ => hcomm a ha b hb
    have := Subgroup.isMulCommutative_closure hpair
    exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : Subgroup.closure T) ⟨y, hy⟩)
  have key : ∀ x ∈ Subgroup.closure T, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h2 x hx
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨k, hk⟩ := ihx
      obtain ⟨l, hl⟩ := ihy
      refine ⟨k + l, ?_⟩
      rw [(Commute.mul_pow (hc x hx y hy) _)]
      rw [pow_add, pow_mul, hk, one_pow, one_mul, mul_comm, pow_mul, hl, one_pow]
    | inv x _ ihx =>
      obtain ⟨k, hk⟩ := ihx
      exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
  intro x
  obtain ⟨k, hk⟩ := key x x.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

omit [Finite G] in
theorem comm_mul_of_comm (a v w : G)
    (h : (a * w * a⁻¹ * w⁻¹) * v = v * (a * w * a⁻¹ * w⁻¹)) :
    a * (v * w) * a⁻¹ * (v * w)⁻¹ = (a * v * a⁻¹ * v⁻¹) * (a * w * a⁻¹ * w⁻¹) := by
  have h' : v * (a * w * a⁻¹ * w⁻¹) * v⁻¹ = a * w * a⁻¹ * w⁻¹ := by
    rw [← h]
    group
  calc a * (v * w) * a⁻¹ * (v * w)⁻¹
      = (a * v * a⁻¹ * v⁻¹) * (v * (a * w * a⁻¹ * w⁻¹) * v⁻¹) := by group
    _ = (a * v * a⁻¹ * v⁻¹) * (a * w * a⁻¹ * w⁻¹) := by rw [h']

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.inf_eq_bot {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hne : L ≠ L')
    {u u' : G} (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u') : L ⊓ L' = ⊥ := by
  by_contra hne'
  have h2 : IsPGroup 2 ↥(L ⊓ L') := (hS.two L hL).to_le inf_le_left
  have hcard : 2 ≤ Nat.card ↥(L ⊓ L') := by
    have h1 : 1 < Nat.card ↥(L ⊓ L') := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne'
    omega
  have h1 := hu.mem_of_le inf_le_left h2 hcard
  have h1' := hu'.mem_of_le inf_le_right h2 hcard
  have hu2 : u * u = 1 := hu.sq
  have huu : u = u' := ((hu'.unique u h1.2 hu2).resolve_left hu.ne_one)
  exact hne (hS.eq_of_uniqueInvolution hL hL' hu (huu ▸ hu'))

omit hS in
theorem isCyclic_of_card_four {L H : Subgroup G} (hHL : H ≤ L) {u : G}
    (hu : IsUniqueInvolution L u) (h4 : Nat.card H = 4) : IsCyclic H := by
  have hex : ∃ x : H, (x : G) ≠ 1 ∧ (x : G) ≠ u := by
    by_contra hno
    push Not at hno
    have hsub : ∀ x : H, (x : G) ∈ ({1, u} : Set G) := by
      intro x
      by_cases hx1 : (x : G) = 1
      · exact Or.inl hx1
      · exact Or.inr (hno x hx1)
    have hinj : Function.Injective (fun x : H => (⟨x, hsub x⟩ : ({1, u} : Set G))) := by
      intro a b hab
      have := congrArg (fun y : ({1, u} : Set G) => (y : G)) hab
      exact Subtype.ext this
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq] at h1
    have h2 : ({1, u} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  obtain ⟨x, hx1, hx2⟩ := hex
  have hx8 : orderOf (x : G) ∣ 4 := by
    rw [← h4, Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard x
  have hxx : (x : G) * x ≠ 1 := by
    intro hsq
    rcases hu.unique x (hHL x.2) hsq with h1 | h1
    · exact hx1 h1
    · exact hx2 h1
  have hord : orderOf x = 4 := by
    rw [← Subgroup.orderOf_coe]
    have : orderOf (x : G) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hx8, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact absurd (by rw [← pow_two, ← h1, pow_orderOf_eq_one]) hxx
    · exact h1
  exact isCyclic_of_orderOf_eq_card x (by rw [hord, h4])

theorem ThinStd.closure_pair_eq {L : Subgroup G} (hL : L ∈ Ω) {u : G}
    (hu : IsUniqueInvolution L u) {a b : G} (ha : a ∈ L) (hb : b ∈ L) (hab : a * b ≠ b * a) :
    Subgroup.closure ({a, b} : Set G) = L := by
  set H := Subgroup.closure ({a, b} : Set G) with hHdef
  have hHL : H ≤ L := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have haH : a ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hbH : b ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have h8 := hS.card L hL
  have hdvd : Nat.card H ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hHL
  have hcard : Nat.card H = 8 := by
    have : Nat.card H ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1 | h1
    · exfalso
      have hbot := (Subgroup.card_eq_one).mp h1
      have ha1 : a = 1 := by
        have := haH
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      exact hab (by rw [ha1, one_mul, mul_one])
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcyc : IsCyclic H := isCyclic_of_prime_card h1
      exact hab (congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨a, haH⟩ ⟨b, hbH⟩))
    · exfalso
      have hcyc : IsCyclic H := isCyclic_of_card_four hHL hu h1
      exact hab (congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨a, haH⟩ ⟨b, hbH⟩))
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge hHL (by rw [hcard, h8])

omit [Finite G] in
theorem ThinStd.exists_not_comm {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  obtain ⟨-, P, hPL, hPnc⟩ := hS.hyp.omega1 L hL
  have hPeq : L = P := hPL.2.2 L le_rfl (hS.two L hL) hPL.1
  by_contra hno
  push Not at hno
  apply hPnc
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact hno x (hPeq ▸ x.2) y (hPeq ▸ y.2)

variable {M : Subgroup G} (hth : ThinAtM Ω M) {z : G} (hz : IsUniqueInvolution M z)
include hth hz

theorem ThinStd.exists_ne_maxAdj {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) :
    ∃ L' : Subgroup G, MaxAdj (nbrAdj Ω) M L' ∧ L' ≠ L := by
  by_contra hno
  push Not at hno
  have hLΩ := hL.1.2.1
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hLΩ
  have hLz := hS.le_centralizer_of_nbrAdj hL.1 hz
  have hnorm : IsNormalTwoIn L z := by
    refine ⟨hLz, hS.two L hLΩ, fun c hc p hp => ?_⟩
    have h1 := hno _ (hS.maxAdj_conj_of_mem hL hz hc)
    rw [← h1]
    exact conj_mem_conjSub hp
  have hLQ := le_Qz hnorm
  have h8 := hS.card L hLΩ
  have hsub : ∀ x : L, (x : G) ∈ ({1, u} : Set G) := by
    intro x
    rcases hS.eq_of_mem_Qz hL.1 (hth L hL) hz hu x.2 (hLQ x.2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hinj : Function.Injective (fun x : L => (⟨x, hsub x⟩ : ({1, u} : Set G))) := by
    intro a b hab
    have := congrArg (fun y : ({1, u} : Set G) => (y : G)) hab
    exact Subtype.ext this
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq] at h1
  have h2 : ({1, u} : Set G).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  omega

variable (hind : Indep Ω M)
include hind

theorem ThinStd.mem_of_centralizes_vM {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) {u : G}
    (hu : IsUniqueInvolution L u) {x : G} (hxL : x ∈ L)
    (hx : ∀ v ∈ vM Ω M, x * v = v * x) : x = 1 ∨ x = u := by
  classical
  set T : Set G := {y | ∃ L' : Subgroup G, MaxAdj (nbrAdj Ω) M L' ∧ y ∈ L' ∧
    ∀ v ∈ vM Ω M, y * v = v * y} with hT
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    rintro a ⟨La, hLa, haL, ha⟩ b ⟨Lb, hLb, hbL, hb⟩
    have hLaΩ := hLa.1.2.1
    have hLbΩ := hLb.1.2.1
    obtain ⟨ua, hua⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hLaΩ
    obtain ⟨ub, hub⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hLbΩ
    by_cases hab : La = Lb
    · subst hab
      obtain ⟨L', hL', hne⟩ := hS.exists_ne_maxAdj hth hz hLa
      obtain ⟨u', hu'⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hL'.1.2.1
      have hu'V : u' ∈ vM Ω M := Subgroup.subset_closure ⟨L', hL', hu'⟩
      have hCU := hS.centralizer_mem_USet hth hind hL' hLa hne hz hu' hua
      obtain ⟨-, -, -, hcyc, -⟩ := hCU
      have haC : a ∈ La ⊓ Subgroup.centralizer ({u'} : Set G) :=
        ⟨haL, Subgroup.mem_centralizer_singleton_iff.mpr (ha u' hu'V)⟩
      have hbC : b ∈ La ⊓ Subgroup.centralizer ({u'} : Set G) :=
        ⟨hbL, Subgroup.mem_centralizer_singleton_iff.mpr (hb u' hu'V)⟩
      have := hcyc.commGroup.mul_comm ⟨a, haC⟩ ⟨b, hbC⟩
      exact congrArg Subtype.val this
    ·
      have hubV : ub ∈ vM Ω M := Subgroup.subset_closure ⟨Lb, hLb, hub⟩
      have huaV : ua ∈ vM Ω M := Subgroup.subset_closure ⟨La, hLa, hua⟩
      have haN : a ∈ Subgroup.normalizer (Lb : Set G) :=
        hS.tight Lb hLbΩ ub hub (Subgroup.mem_centralizer_singleton_iff.mpr (ha ub hubV))
      have hbN : b ∈ Subgroup.normalizer (La : Set G) :=
        hS.tight La hLaΩ ua hua (Subgroup.mem_centralizer_singleton_iff.mpr (hb ua huaV))
      have h1 : a * b * a⁻¹ * b⁻¹ ∈ La := by
        have : b * a⁻¹ * b⁻¹ ∈ La := (Subgroup.mem_normalizer_iff.mp hbN _).mp (La.inv_mem haL)
        have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
        rw [e]
        exact La.mul_mem haL this
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ Lb := by
        have : a * b * a⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp haN _).mp hbL
        exact Lb.mul_mem this (Lb.inv_mem hbL)
      have hbot := hS.inf_eq_bot hLaΩ hLbΩ hab hua hub
      have h3 : a * b * a⁻¹ * b⁻¹ ∈ La ⊓ Lb := ⟨h1, h2⟩
      rw [hbot, Subgroup.mem_bot] at h3
      calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
        _ = b * a := by rw [h3]; group
  have h2T : ∀ a ∈ T, ∃ k : ℕ, a ^ 2 ^ k = 1 := by
    rintro a ⟨La, hLa, haL, -⟩
    obtain ⟨k, hk⟩ := hS.two La hLa.1.2.1 ⟨a, haL⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hnorm : IsNormalTwoIn (Subgroup.closure T) z := by
    refine ⟨(Subgroup.closure_le _).mpr ?_, isPGroup_closure_of_comm hcomm h2T, ?_⟩
    · rintro a ⟨La, hLa, haL, -⟩
      exact hS.le_centralizer_of_nbrAdj hLa.1 hz haL
    · intro c hc p hp
      have hle : conjSub c (Subgroup.closure T) ≤ Subgroup.closure T := by
        rw [conjSub, MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨a, ⟨La, hLa, haL, ha⟩, rfl⟩
        refine ⟨conjSub c La, hS.maxAdj_conj_of_mem hLa hz hc, conj_mem_conjSub haL, ?_⟩
        intro v hv
        have hv' : c⁻¹ * v * c ∈ vM Ω M := by
          have h1 : v ∈ conjSub c (vM Ω M) := by rw [hS.conjSub_vM hz hc]; exact hv
          rw [mem_conjSub_iff] at h1
          exact h1
        have h1 := ha _ hv'
        show c * a * c⁻¹ * v = v * (c * a * c⁻¹)
        calc c * a * c⁻¹ * v = c * (a * (c⁻¹ * v * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * v * c) * a) * c⁻¹ := by rw [h1]
          _ = v * (c * a * c⁻¹) := by group
      exact hle (conj_mem_conjSub hp)
  have hxQ : x ∈ Qz z := le_Qz hnorm (Subgroup.subset_closure ⟨L, hL, hxL, hx⟩)
  exact hS.eq_of_mem_Qz hL.1 (hth L hL) hz hu hxL hxQ

theorem ThinStd.card_vM_eq {L : Subgroup G} (hL : MaxAdj (nbrAdj Ω) M L) :
    Nat.card (vM Ω M) = 8 := by
  classical
  have hLΩ := hL.1.2.1
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hLΩ
  obtain ⟨a, ha, b, hb, hab⟩ := hS.exists_not_comm hLΩ
  have hgen := hS.closure_pair_eq hLΩ hu ha hb hab
  have huV : u ∈ vM Ω M := Subgroup.subset_closure ⟨L, hL, hu⟩
  have hcV := hS.vM_comm hth hind hz
  have hcm : ∀ l ∈ L, ∀ v ∈ vM Ω M, l * v * l⁻¹ * v⁻¹ = 1 ∨ l * v * l⁻¹ * v⁻¹ = u :=
    fun l hl v hv => hS.comm_vM hth hind hz hL hu hv hl
  have hcomm_u : ∀ v ∈ vM Ω M, ∀ x ∈ vM Ω M, ∀ l ∈ L,
      (l * x * l⁻¹ * x⁻¹) * v = v * (l * x * l⁻¹ * x⁻¹) := by
    intro v hv x hx l hl
    rcases hcm l hl x hx with h | h
    · rw [h]; group
    · rw [h]; exact hcV u huV v hv
  let f : ↥(vM Ω M) →* G × G :=
    { toFun := fun v => (a * v * a⁻¹ * (v : G)⁻¹, b * v * b⁻¹ * (v : G)⁻¹)
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [Subgroup.coe_mul, Prod.mk_mul_mk]
        rw [comm_mul_of_comm a v w (hcomm_u v v.2 w w.2 a ha),
          comm_mul_of_comm b v w (hcomm_u v v.2 w w.2 b hb)] }
  have huc : ∀ l ∈ L, l * u * l⁻¹ = u := fun l hl =>
    hu.conj_eq (conjSub_eq_self_of_mem hl)
  have huc' : ∀ l ∈ L, l * u = u * l := fun l hl => by
    calc l * u = (l * u * l⁻¹) * l := by group
      _ = u * l := by rw [huc l hl]
  have hcent_of : ∀ x : G, ∀ v : G, x * v * x⁻¹ * v⁻¹ = 1 → x * v = v * x := by
    intro x v h1
    calc x * v = (x * v * x⁻¹ * v⁻¹) * v * x := by group
      _ = v * x := by rw [h1]; group
  have hker : ∀ v : ↥(vM Ω M), v ∈ f.ker → (v : G) = 1 ∨ (v : G) = u := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    have h1 : a * v * a⁻¹ * (v : G)⁻¹ = 1 := congrArg Prod.fst hv
    have h2 : b * v * b⁻¹ * (v : G)⁻¹ = 1 := congrArg Prod.snd hv
    have hLc : L ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent_of _ _ h1)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent_of _ _ h2)
    exact hS.eq_of_centralizes hth hind hz hL hu v.2
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
  have hkercard : Nat.card f.ker ≤ 2 := by
    have hsub : ∀ v : f.ker, ((v : ↥(vM Ω M)) : G) ∈ ({1, u} : Set G) := fun v =>
      (hker v.1 v.2).elim (fun h => Or.inl h) (fun h => Or.inr h)
    have hinj : Function.Injective
        (fun v : f.ker => (⟨(v : ↥(vM Ω M)), hsub v⟩ : ({1, u} : Set G))) := by
      intro x y hxy
      have := congrArg (fun y : ({1, u} : Set G) => (y : G)) hxy
      exact Subtype.ext (Subtype.ext this)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq] at h1
    have h2 : ({1, u} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  have hrangemem : ∀ v : ↥(vM Ω M), f v ∈ (({1, u} : Set G) ×ˢ ({1, u} : Set G)) := by
    intro v
    refine ⟨?_, ?_⟩
    · rcases hcm a ha v v.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases hcm b hb v v.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hrange : Nat.card f.range ≤ 4 := by
    have hsub : ∀ w : f.range, (w : G × G) ∈ (({1, u} : Set G) ×ˢ ({1, u} : Set G)) := by
      rintro ⟨_, v, rfl⟩
      exact hrangemem v
    have hinj : Function.Injective (fun w : f.range =>
        (⟨w, hsub w⟩ : (({1, u} : Set G) ×ˢ ({1, u} : Set G) : Set (G × G)))) := by
      intro x y hxy
      have := congrArg (fun y : (({1, u} : Set G) ×ˢ ({1, u} : Set G) : Set (G × G)) =>
        (y : G × G)) hxy
      exact Subtype.ext this
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq, Set.ncard_prod] at h1
    have h2 : ({1, u} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    nlinarith
  have htot := Subgroup.card_ker_mul_card_range f
  have hV2 : IsPGroup 2 ↥(vM Ω M) :=
    isPGroup_closure_of_comm (hS.invs_comm hth hind hz) (fun x ⟨L', _, hx⟩ => ⟨1, by
      rw [pow_one, pow_two]; exact hx.sq⟩)
  obtain ⟨L', hL', hne⟩ := hS.exists_ne_maxAdj hth hz hL
  obtain ⟨u', hu'⟩ := Sec6Gen.exists_uniqueInvolution hS.hyp hL'.1.2.1
  have hu'V : u' ∈ vM Ω M := Subgroup.subset_closure ⟨L', hL', hu'⟩
  have huu' : u ≠ u' := by
    intro h
    exact hne (hS.eq_of_uniqueInvolution hL'.1.2.1 hLΩ hu' (h ▸ hu))
  have h3 : 3 ≤ Nat.card ↥(vM Ω M) := by
    have hsub : ({1, u, u'} : Set G) ⊆ (vM Ω M : Set G) := by
      rintro x (rfl | rfl | rfl)
      · exact (vM Ω M).one_mem
      · exact huV
      · exact hu'V
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have e : (vM Ω M : Set G).ncard = Nat.card ↥(vM Ω M) := (Nat.card_coe_set_eq _).symm
    have h2 : ({1, u, u'} : Set G).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, u, u', hu.ne_one.symm, hu'.ne_one.symm, huu', rfl⟩
    rw [h2, e] at h1
    exact h1
  have hle8 : Nat.card ↥(vM Ω M) ≤ 8 := by
    rw [← htot]
    exact (Nat.mul_le_mul hkercard hrange).trans (by norm_num)
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hk3 : k = 2 ∨ k = 3 := by
    rw [hk] at h3 hle8
    have hk4 : k < 4 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    interval_cases k
    · norm_num at h3
    · norm_num at h3
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hk3 with rfl | rfl
  swap
  · rw [hk]; norm_num
  ·
    exfalso
    have hu1 : (⟨u, huV⟩ : ↥(vM Ω M)) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      show (a * u * a⁻¹ * u⁻¹, b * u * b⁻¹ * u⁻¹) = (1, 1)
      rw [huc a ha, huc b hb, mul_inv_cancel]
    have hker2 : 2 ≤ Nat.card f.ker := by
      have h1 : 1 < Nat.card f.ker := by
        rw [Subgroup.one_lt_card_iff_ne_bot]
        intro hbot
        have := hu1
        rw [hbot, Subgroup.mem_bot] at this
        exact hu.ne_one (congrArg Subtype.val this)
      omega
    have hr2 : Nat.card f.range = 2 := by
      have hk2 : Nat.card f.ker = 2 := le_antisymm hkercard hker2
      have h4 : Nat.card f.ker * Nat.card f.range = 4 := by rw [htot, hk]; norm_num
      rw [hk2] at h4
      omega
    obtain ⟨r, hr⟩ : ∃ r : f.range, r ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : f.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        exact congrArg Subtype.val (hno ⟨x, hx⟩)
      rw [hbot, Subgroup.card_bot] at hr2
      omega
    have hrange2 : ∀ w : f.range, w = 1 ∨ w = r := by
      intro w
      by_contra hno
      push Not at hno
      have h1 : 3 ≤ Nat.card f.range := by
        have hsub : ({1, r, w} : Set f.range) ⊆ Set.univ := Set.subset_univ _
        have h2 := Set.ncard_le_ncard hsub
        rw [Set.ncard_univ] at h2
        have h3 : ({1, r, w} : Set f.range).ncard = 3 := by
          rw [Set.ncard_eq_three]
          exact ⟨1, r, w, Ne.symm hr, Ne.symm hno.1, Ne.symm hno.2, rfl⟩
        omega
      omega
    have hval : ∀ v : ↥(vM Ω M), f v = 1 ∨ f v = (r : G × G) := by
      intro v
      rcases hrange2 ⟨f v, v, rfl⟩ with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    have hr' : (r : G × G) ∈ (({1, u} : Set G) ×ˢ ({1, u} : Set G)) := by
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp r.2
      rw [← hv]
      exact hrangemem v
    have hnotcen : ∀ x ∈ L, x * a ≠ a * x ∨ x * b ≠ b * x → ¬ (x = 1 ∨ x = u) := by
      rintro x - hx (rfl | rfl)
      · rcases hx with h | h <;> exact h (by group)
      · rcases hx with h | h
        · exact h (huc' a ha).symm
        · exact h (huc' b hb).symm
    rcases hr' with ⟨h1 | h1, h2 | h2⟩
    · exact hr (Subtype.ext (Prod.ext h1 h2))
    ·
      have hcen : ∀ v ∈ vM Ω M, a * v = v * a := by
        intro v hv
        refine hcent_of a v ?_
        rcases hval ⟨v, hv⟩ with h | h
        · exact congrArg Prod.fst h
        · exact (congrArg Prod.fst h).trans h1
      exact hnotcen a ha (Or.inr hab)
        (hS.mem_of_centralizes_vM hth hz hind hL hu ha hcen)
    ·
      have hcen : ∀ v ∈ vM Ω M, b * v = v * b := by
        intro v hv
        refine hcent_of b v ?_
        rcases hval ⟨v, hv⟩ with h | h
        · exact congrArg Prod.snd h
        · exact (congrArg Prod.snd h).trans h2
      exact hnotcen b hb (Or.inl (Ne.symm hab))
        (hS.mem_of_centralizes_vM hth hz hind hL hu hb hcen)
    ·
      have hcen : ∀ v ∈ vM Ω M, (a * b) * v = v * (a * b) := by
        intro v hv
        refine hcent_of (a * b) v ?_
        have heq : a * v * a⁻¹ * v⁻¹ = b * v * b⁻¹ * v⁻¹ := by
          rcases hval ⟨v, hv⟩ with h | h
          · exact (congrArg Prod.fst h).trans (congrArg Prod.snd h).symm
          · exact ((congrArg Prod.fst h).trans h1).trans ((congrArg Prod.snd h).trans h2).symm
        have hbc : a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ = b * v * b⁻¹ * v⁻¹ := by
          rcases hcm b hb v hv with h | h
          · rw [h]; group
          · rw [h]; exact huc a ha
        have hsq : (a * v * a⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) = 1 := by
          rcases hcm a ha v hv with h | h
          · rw [h]; group
          · rw [h]; exact hu.sq
        calc a * b * v * (a * b)⁻¹ * v⁻¹
            = (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
          _ = (b * v * b⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) := by rw [hbc]
          _ = (a * v * a⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) := by rw [heq]
          _ = 1 := hsq
      have hab' : a * b ∈ L := L.mul_mem ha hb
      have hnc : (a * b) * a ≠ a * (a * b) ∨ (a * b) * b ≠ b * (a * b) := by
        left
        intro h
        apply hab
        have h' : a * (b * a) = a * (a * b) := by rw [← mul_assoc, h]
        exact (mul_left_cancel h').symm
      exact hnotcen (a * b) hab' hnc (hS.mem_of_centralizes_vM hth hz hind hL hu hab' hcen)

end CFSG.ClassicalInvolution.Q3.TC.Thin
