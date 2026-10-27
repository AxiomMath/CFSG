module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Cases

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type*} [Group G] [Finite G] {j : ℕ}

structure MainData (c : Cfg G j) where
  hj : j = 3
  hJ9 : Nat.card c.J = 9
  n₀ : G
  hn₀N : n₀ ∈ c.N
  hn₀J : n₀ ∉ c.J
  hgen : c.N = c.J ⊔ Subgroup.zpowers n₀
  hsurj : ∀ x ∈ c.J, ∃ s ∈ c.S, s * n₀ * s⁻¹ * n₀⁻¹ = x
  hcs : ∀ s ∈ c.S, s * n₀ = n₀ * s → s ∈ c.J

namespace MainData

variable {c : Cfg G j} (d : MainData c)

include d

theorem hS81 : Nat.card c.S = 81 := by rw [c.hSc, d.hj]; norm_num

theorem hN27 : Nat.card c.N = 27 := by rw [c.hNc, d.hj]; norm_num

omit d in
theorem J_normalized {m : G} (hm : m ∈ c.M) {x : G} (hx : x ∈ c.J) : m * x * m⁻¹ ∈ c.J := by
  have := c.hMn
  have := c.hNn
  exact ⟨c.hSn m hm x hx.1, Subgroup.Normal.conj_mem c.hNn x hx.2 m⟩

theorem comm_NM : ∀ m ∈ c.M, ∀ n ∈ c.N, m * n * m⁻¹ * n⁻¹ ∈ c.J := by
  classical
  have hMn := c.hMn
  have hNn := c.hNn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxN, hxJ, hxm⟩ := exists_mem_central_mod_of_normalizes (p := 3) c.pM c.hNM
    (fun m hm a ha => J_normalized hm ha)
    (fun m _ b hb => Subgroup.Normal.conj_mem hNn b hb m) c.J_lt_N
  let H : Subgroup G :=
    { carrier := {n | n ∈ c.N ∧ ∀ m ∈ c.M, m * n * m⁻¹ * n⁻¹ ∈ c.J}
      one_mem' := ⟨c.N.one_mem, fun m _ => by simp⟩
      mul_mem' := by
        rintro n n' ⟨hn, hnm⟩ ⟨hn', hn'm⟩
        refine ⟨c.N.mul_mem hn hn', fun m hm => ?_⟩
        have h1 : m * (n * n') * m⁻¹ * (n * n')⁻¹ =
            (m * n * m⁻¹ * n⁻¹) * (n * (m * n' * m⁻¹ * n'⁻¹) * n⁻¹) := by group
        rw [h1]
        have hk := hn'm m hm
        have hcomm : n * (m * n' * m⁻¹ * n'⁻¹) * n⁻¹ = m * n' * m⁻¹ * n'⁻¹ := by
          have := c.hN.1 n hn _ (c.J_le_N hk)
          rw [mul_inv_eq_iff_eq_mul]
          exact this
        rw [hcomm]
        exact c.J.mul_mem (hnm m hm) hk
      inv_mem' := by
        rintro n ⟨hn, hnm⟩
        refine ⟨c.N.inv_mem hn, fun m hm => ?_⟩
        have hk := hnm m hm
        have h1 : m * n⁻¹ * m⁻¹ * (n⁻¹)⁻¹ = n⁻¹ * (m * n * m⁻¹ * n⁻¹)⁻¹ * n := by group
        rw [h1]
        have hcomm : n⁻¹ * (m * n * m⁻¹ * n⁻¹)⁻¹ * n = (m * n * m⁻¹ * n⁻¹)⁻¹ := by
          have h2 := c.hN.1 n hn _ (c.J_le_N (c.J.inv_mem hk))
          calc n⁻¹ * (m * n * m⁻¹ * n⁻¹)⁻¹ * n
              = n⁻¹ * ((m * n * m⁻¹ * n⁻¹)⁻¹ * n) := by rw [mul_assoc]
            _ = n⁻¹ * (n * (m * n * m⁻¹ * n⁻¹)⁻¹) := by rw [← h2]
            _ = (m * n * m⁻¹ * n⁻¹)⁻¹ := by group
        rw [hcomm]
        exact c.J.inv_mem hk }
  have hxH : x ∈ H := ⟨hxN, hxm⟩
  have hJH : c.J ≤ H := fun y hy =>
    ⟨c.J_le_N hy, fun m hm => c.J.mul_mem (J_normalized hm hy) (c.J.inv_mem hy)⟩
  have hgen := c.N_eq_sup (i := 2) (by rw [d.hJ9]; norm_num) (by rw [d.hN27]; norm_num) hxN hxJ
  have hNH : c.N ≤ H := by
    rw [hgen]
    exact sup_le hJH (Subgroup.zpowers_le.mpr hxH)
  intro m hm n hn
  exact (hNH hn).2 m hm


theorem J_normal : c.J.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨s, hs, rfl⟩ := d.hsurj x hx
  have hMn := c.hMn
  have hsM : s ∈ c.M := c.hSM hs
  have hn₀ : g * d.n₀ * g⁻¹ ∈ c.N := Subgroup.Normal.conj_mem c.hNn _ d.hn₀N g
  have := d.comm_NM (g * s * g⁻¹) (Subgroup.Normal.conj_mem hMn s hsM g) _ hn₀
  have e : g * (s * d.n₀ * s⁻¹ * d.n₀⁻¹) * g⁻¹ =
      g * s * g⁻¹ * (g * d.n₀ * g⁻¹) * (g * s * g⁻¹)⁻¹ * (g * d.n₀ * g⁻¹)⁻¹ := by group
  rw [e]; exact this

theorem J_central : ∀ m ∈ c.M, ∀ x ∈ c.J, m * x = x * m := by
  have hJn := d.J_normal
  have hMn := c.hMn
  let T : Subgroup G := c.M ⊓ Subgroup.centralizer (c.J : Set G)
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ⟨Subgroup.Normal.conj_mem hMn t ht.1 g, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ c.J := Subgroup.Normal.conj_mem hJn h hh g⁻¹
    have h1 := Subgroup.mem_centralizer_iff.mp ht.2 _ hh'
    calc h * (g * t * g⁻¹) = g * ((g⁻¹ * h * g⁻¹⁻¹) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * h := by group
  have hST : c.S ≤ T := fun s hs =>
    ⟨c.hSM hs, Subgroup.mem_centralizer_iff.mpr fun h hh => c.hS.1 h (c.J_le_S hh) s hs⟩
  have hTM : T = c.M := c.hmin T inf_le_left hTn hST
  intro m hm x hx
  have : m ∈ T := hTM ▸ hm
  exact (Subgroup.mem_centralizer_iff.mp this.2 x hx).symm

theorem S_comm_M : ∀ s ∈ c.S, ∀ m ∈ c.M, m * s * m⁻¹ * s⁻¹ ∈ c.J := by
  intro s hs m hm
  set a := m * s * m⁻¹ with ha_def
  have haS : a ∈ c.S := c.hSn m hm s hs
  have hk : s * d.n₀ * s⁻¹ * d.n₀⁻¹ ∈ c.J := c.comm_mem hs d.hn₀N
  have hka : a * d.n₀ * a⁻¹ * d.n₀⁻¹ ∈ c.J := c.comm_mem haS d.hn₀N
  have hj' : m * d.n₀ * m⁻¹ * d.n₀⁻¹ ∈ c.J := d.comm_NM m hm _ d.hn₀N
  set j' := m * d.n₀ * m⁻¹ * d.n₀⁻¹ with hj'_def
  have hmn : m * d.n₀ * m⁻¹ = j' * d.n₀ := by rw [hj'_def]; group
  have h1 : m * (s * d.n₀ * s⁻¹ * d.n₀⁻¹) * m⁻¹ = s * d.n₀ * s⁻¹ * d.n₀⁻¹ := by
    have := d.J_central m hm _ hk
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have h2 : m * (s * d.n₀ * s⁻¹ * d.n₀⁻¹) * m⁻¹ =
      (a * j' * a⁻¹) * (a * d.n₀ * a⁻¹ * d.n₀⁻¹) * j'⁻¹ := by
    have e : m * (s * d.n₀ * s⁻¹ * d.n₀⁻¹) * m⁻¹ =
        a * (m * d.n₀ * m⁻¹) * a⁻¹ * (m * d.n₀ * m⁻¹)⁻¹ := by
      rw [ha_def]; group
    rw [e, hmn]; group
  have h3 : a * j' * a⁻¹ = j' := by
    have := c.hS.1 a haS j' (c.J_le_S hj')
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have h4 : j' * (a * d.n₀ * a⁻¹ * d.n₀⁻¹) * j'⁻¹ = a * d.n₀ * a⁻¹ * d.n₀⁻¹ := by
    have := c.hS.1 j' (c.J_le_S hj') _ (c.J_le_S hka)
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have hkk : a * d.n₀ * a⁻¹ * d.n₀⁻¹ = s * d.n₀ * s⁻¹ * d.n₀⁻¹ := by
    rw [← h1, h2, h3, h4]
  have h5 : a * d.n₀ * a⁻¹ = s * d.n₀ * s⁻¹ := mul_right_cancel hkk
  have hcomm : (s⁻¹ * a) * d.n₀ = d.n₀ * (s⁻¹ * a) := by
    calc s⁻¹ * a * d.n₀ = s⁻¹ * (a * d.n₀ * a⁻¹) * a := by group
      _ = s⁻¹ * (s * d.n₀ * s⁻¹) * a := by rw [h5]
      _ = d.n₀ * (s⁻¹ * a) := by group
  have hw : s⁻¹ * a ∈ c.J := d.hcs _ (c.S.mul_mem (c.S.inv_mem hs) haS) hcomm
  have hsw : s * (s⁻¹ * a) = (s⁻¹ * a) * s := c.hS.1 s hs _ (c.J_le_S hw)
  have : m * s * m⁻¹ * s⁻¹ = s⁻¹ * a := by
    calc m * s * m⁻¹ * s⁻¹ = a * s⁻¹ := by rw [ha_def]
      _ = s * (s⁻¹ * a) * s⁻¹ := by group
      _ = (s⁻¹ * a) * s * s⁻¹ := by rw [hsw]
      _ = s⁻¹ * a := by group
  rw [this]; exact hw


theorem M_comm : ∀ x ∈ c.M, ∀ y ∈ c.M, x * y * x⁻¹ * y⁻¹ ∈ c.J := by
  have hJn := d.J_normal
  have hMn := c.hMn
  let Z : Subgroup G :=
    { carrier := {x | x ∈ c.M ∧ ∀ y ∈ c.M, x * y * x⁻¹ * y⁻¹ ∈ c.J}
      one_mem' := ⟨c.M.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro x x' ⟨hx, hxc⟩ ⟨hx', hx'c⟩
        refine ⟨c.M.mul_mem hx hx', fun y hy => ?_⟩
        have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
            (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
        rw [e]
        exact c.J.mul_mem (Subgroup.Normal.conj_mem hJn _ (hx'c y hy) x) (hxc y hy)
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨c.M.inv_mem hx, fun y hy => ?_⟩
        have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact Subgroup.Normal.conj_mem hJn _ (c.J.inv_mem (hxc y hy)) x⁻¹ }
  have hZn : Z.Normal := by
    refine ⟨fun z hz g => ⟨Subgroup.Normal.conj_mem hMn z hz.1 g, fun y hy => ?_⟩⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ c.M := Subgroup.Normal.conj_mem hMn y hy g⁻¹
    have := hz.2 _ hy'
    have e : g * z * g⁻¹ * y * (g * z * g⁻¹)⁻¹ * y⁻¹ =
        g * (z * (g⁻¹ * y * g⁻¹⁻¹) * z⁻¹ * (g⁻¹ * y * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact Subgroup.Normal.conj_mem hJn _ this g
  have hSZ : c.S ≤ Z := fun s hs => ⟨c.hSM hs, fun y hy => by
    have := c.J.inv_mem (d.S_comm_M s hs y hy)
    have e : (y * s * y⁻¹ * s⁻¹)⁻¹ = s * y * s⁻¹ * y⁻¹ := by group
    rwa [e] at this⟩
  have hZM : Z = c.M := c.hmin Z (fun z hz => hz.1) hZn hSZ
  intro x hx y hy
  have : x ∈ Z := hZM ▸ hx
  exact this.2 y hy

theorem M_exp : ∀ x ∈ c.M, x ^ 3 = 1 := by
  have hMn := c.hMn
  let E : Subgroup G :=
    { carrier := {x | x ∈ c.M ∧ x ^ 3 = 1}
      one_mem' := ⟨c.M.one_mem, one_pow 3⟩
      mul_mem' := by
        rintro x y ⟨hx, hx3⟩ ⟨hy, hy3⟩
        refine ⟨c.M.mul_mem hx hy, ?_⟩
        have hc : (x * y)⁻¹ * (y * x) ∈ c.J := by
          have := d.M_comm y⁻¹ (c.M.inv_mem hy) x⁻¹ (c.M.inv_mem hx)
          have e : y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ = (x * y)⁻¹ * (y * x) := by group
          rwa [e] at this
        have hcx : (x * y)⁻¹ * (y * x) * x = x * ((x * y)⁻¹ * (y * x)) :=
          (d.J_central x hx _ hc).symm
        have hcy : (x * y)⁻¹ * (y * x) * y = y * ((x * y)⁻¹ * (y * x)) :=
          (d.J_central y hy _ hc).symm
        have hrel : y * x = x * y * ((x * y)⁻¹ * (y * x)) := by group
        have := mul_pow_three_of_comm hrel hcx hcy
        rw [this, hx3, hy3, c.hN.2 _ (c.J_le_N hc)]
        simp
      inv_mem' := by
        rintro x ⟨hx, hx3⟩
        exact ⟨c.M.inv_mem hx, by rw [inv_pow, hx3, inv_one]⟩ }
  have hEn : E.Normal := by
    refine ⟨fun z hz g => ⟨Subgroup.Normal.conj_mem hMn z hz.1 g, ?_⟩⟩
    rw [conj_pow, hz.2]; simp
  have hSE : c.S ≤ E := fun s hs => ⟨c.hSM hs, c.hS.2 s hs⟩
  have hEM : E = c.M := c.hmin E (fun z hz => hz.1) hEn hSE
  intro x hx
  have : x ∈ E := hEM ▸ hx
  exact this.2


theorem C_M_le_N : ∀ x ∈ c.M, (∀ n ∈ c.N, x * n = n * x) → x ∈ c.N := by
  classical
  have hMn := c.hMn
  have hNn := c.hNn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hxM hxc
  by_contra hxN
  let C : Subgroup G := c.M ⊓ Subgroup.centralizer (c.N : Set G)
  have hCn : C.Normal := by
    refine ⟨fun t ht g => ⟨Subgroup.Normal.conj_mem hMn t ht.1 g, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have hh' : g⁻¹ * h * g⁻¹⁻¹ ∈ c.N := Subgroup.Normal.conj_mem hNn h hh g⁻¹
    have h1 := Subgroup.mem_centralizer_iff.mp ht.2 _ hh'
    calc h * (g * t * g⁻¹) = g * ((g⁻¹ * h * g⁻¹⁻¹) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * h * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * h := by group
  have hxC : x ∈ C := ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun h hh => (hxc h hh).symm⟩
  have hCNn : (C ⊓ c.N).Normal := ⟨fun t ht g => ⟨Subgroup.Normal.conj_mem hCn t ht.1 g,
    Subgroup.Normal.conj_mem hNn t ht.2 g⟩⟩
  have hlt : C ⊓ c.N < C := lt_of_le_of_ne inf_le_left (fun h => hxN (by
    have : x ∈ C ⊓ c.N := by rw [h]; exact hxC
    exact this.2))
  obtain ⟨y, hyC, hyA, hyg⟩ := exists_mem_central_mod c.hG hlt
  apply hyA
  refine ⟨hyC, c.ext_mem hyC.1 (fun n hn => (Subgroup.mem_centralizer_iff.mp hyC.2 n hn).symm)
    (fun m _ => (hyg m).2) (d.M_exp y hyC.1)⟩

theorem card_M_le : Nat.card c.M ≤ 243 := by
  have hJM : c.J ≤ c.M := c.J_le_S.trans c.hSM
  have h1 := card_le_card_inf_centralizer_mul c.M c.J (fun a ha x hx => d.J_central a ha x hx)
    hJM d.n₀ (fun s hs => d.comm_NM s hs d.n₀ d.hn₀N)
  have h2 : Nat.card (c.M ⊓ Subgroup.centralizer {d.n₀} : Subgroup G) ≤ 27 := by
    rw [← d.hN27]
    apply Subgroup.card_le_of_le
    intro x hx
    obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxc' : d.n₀ * x = x * d.n₀ := Subgroup.mem_centralizer_iff.mp hxc d.n₀ rfl
    refine d.C_M_le_N x hxM fun n hn => ?_
    have hle : c.J ⊔ Subgroup.zpowers d.n₀ ≤ Subgroup.centralizer {x} := by
      refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact d.J_central h hxM y hy
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hxc'.symm
    have := hle (d.hgen ▸ hn)
    exact Subgroup.mem_centralizer_iff.mp this x rfl
  rw [d.hJ9] at h1
  calc Nat.card c.M ≤ _ := h1
    _ ≤ 27 * 9 := Nat.mul_le_mul_right 9 h2
    _ = 243 := by norm_num

theorem card_M_eq : Nat.card c.M = 3 ^ 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp c.pM
  have hle := d.card_M_le
  have hSle := Subgroup.card_le_of_le c.hSM
  rw [d.hS81] at hSle
  have h81 : Nat.card c.M ≠ 81 := by
    intro h
    have hSM : c.S = c.M := Subgroup.eq_of_le_of_card_ge c.hSM (by rw [h, d.hS81])
    apply c.hno c.S c.hSM (hSM ▸ c.hMn) c.hS
    rw [c.hSc]
  rw [ht] at hle hSle h81 ⊢
  have ht5 : t ≤ 5 := by
    by_contra h
    have : 3 ^ 6 ≤ 3 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ht4 : 4 ≤ t := by
    by_contra h
    have : 3 ^ t ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases t
  · simp at h81
  · rfl


theorem false_main : False := by
  classical
  have hMn := c.hMn
  have hS81 := d.hS81
  have hM243 : Nat.card c.M = 3 ^ (4 + 1) := d.card_M_eq
  have hall : ∀ g : G, c.S.map (MulAut.conj g).toMonoidHom = c.S := by
    intro g
    by_contra hne
    set S' : Subgroup G := c.S.map (MulAut.conj g).toMonoidHom with hS'
    have hmemS' : ∀ x, x ∈ S' ↔ ∃ s ∈ c.S, g * s * g⁻¹ = x := by
      intro x
      simp only [hS', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hS'M : S' ≤ c.M := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := (hmemS' x).mp hx
      exact Subgroup.Normal.conj_mem hMn s (c.hSM hs) g
    have hcardS' : Nat.card S' = 81 := by
      rw [hS', Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hS81
    have hS'ab : ∀ a ∈ S', ∀ b ∈ S', a * b = b * a := by
      intro a ha b hb
      obtain ⟨s, hs, rfl⟩ := (hmemS' a).mp ha
      obtain ⟨t, ht, rfl⟩ := (hmemS' b).mp hb
      have := c.hS.1 s hs t ht
      calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
        _ = g * (t * s) * g⁻¹ := by rw [this]
        _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
    have hS'n : ∀ m ∈ c.M, ∀ x ∈ S', m * x * m⁻¹ ∈ S' := by
      intro m hm x hx
      obtain ⟨s, hs, rfl⟩ := (hmemS' x).mp hx
      refine (hmemS' _).mpr ⟨(g⁻¹ * m * g) * s * (g⁻¹ * m * g)⁻¹, ?_, by group⟩
      exact c.hSn _ (by simpa using Subgroup.Normal.conj_mem hMn m hm g⁻¹) s hs
    have hlt : c.S < c.S ⊔ S' := by
      refine lt_of_le_of_ne le_sup_left (fun h => hne ?_)
      have hle : S' ≤ c.S := by rw [h]; exact le_sup_right
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS', hS81])
    have hsup : c.S ⊔ S' = c.M :=
      eq_of_lt_of_le_card (A := c.S) (i := 4) hlt (sup_le c.hSM hS'M)
        (by rw [hS81]; norm_num) hM243
    have hAJ : c.S ⊓ S' ≤ c.J := by
      intro a ha
      have hle : c.S ⊔ S' ≤ Subgroup.centralizer {a} := by
        refine sup_le (fun s hs => ?_) (fun s hs => ?_)
        · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact c.hS.1 _ ha.1 s hs
        · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact hS'ab _ ha.2 s hs
      have haN : a ∈ c.N := c.centralizer_le ha.1 fun n hn => by
        have := hle (hsup ▸ c.hNM hn)
        exact (Subgroup.mem_centralizer_iff.mp this a rfl).symm.symm
      exact ⟨ha.1, haN⟩
    have h2 := Subgroup.relIndex_mul_card (H := S') (K := c.M)
    rw [inf_of_le_left hS'M, hcardS', hM243] at h2
    have h4 : S'.relIndex c.M = 3 := by omega
    have h1 : S'.relIndex c.S ≤ S'.relIndex c.M :=
      Subgroup.relIndex_le_of_le_right c.hSM (by rw [h4]; norm_num)
    have h3 := Subgroup.relIndex_mul_card (H := S') (K := c.S)
    rw [inf_comm, hS81] at h3
    have h5 : 27 ≤ Nat.card (c.S ⊓ S' : Subgroup G) := by
      by_contra hlt27
      have hlt27 := not_le.mp hlt27
      have : S'.relIndex c.S * Nat.card (c.S ⊓ S' : Subgroup G) ≤ 3 * 26 :=
        Nat.mul_le_mul (h1.trans h4.le) (by omega)
      omega
    have h6 := Subgroup.card_le_of_le hAJ
    rw [d.hJ9] at h6
    omega
  apply c.hno c.S c.hSM ?_ c.hS c.hSc
  refine ⟨fun s hs g => ?_⟩
  have h1 : g * s * g⁻¹ ∈ c.S.map (MulAut.conj g).toMonoidHom :=
    ⟨s, hs, by simp [MulAut.conj_apply]⟩
  rwa [hall g] at h1

end MainData

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
