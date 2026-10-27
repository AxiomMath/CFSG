module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Gen
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Aux
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Basic

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer_of_normalizer {V : Subgroup G} {m : G}
    (hm : ∀ v, v ∈ V ↔ m * v * m⁻¹ ∈ V) {c : G} (hc : c ∈ centralizer (V : Set G)) :
    m * c * m⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : m⁻¹ * v * m ∈ V := by
    refine (hm (m⁻¹ * v * m)).2 ?_
    have e : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
    rw [e]
    exact hv
  have hcv := mem_centralizer_iff.1 hc _ hv'
  calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [hcv]
    _ = (m * c * m⁻¹) * v := by group

@[expose] def qwSub {d : Datum A} {α : ℕ} (c : Chart4 d α) : Subgroup G := d.Q ⊔ c.W

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem exists_rep (k : Kind) : ∃ y, K.c.rep k = some y := by
  have hk : k ∈ K.c.kinds := by rw [K.kin]; trivial
  exact Option.isSome_iff_exists.1 hk

theorem Q_comm {a b : G} (ha : a ∈ d.Q) (hb : b ∈ d.Q) : a * b = b * a := by
  have : IsCyclic d.Q := d.Q_isCyclic K.h
  have := IsCyclic.isMulCommutative (α := d.Q)
  exact setLike_mul_comm ha hb

theorem Q_le_centralizer_W : d.Q ≤ centralizer (K.c.W : Set G) := fun u hu => by
  rw [mem_centralizer_iff]
  intro _ hw
  exact d.comm_Q_S hu hw.1

theorem mem_qwSub_iff {x : G} : x ∈ qwSub K.c ↔ ∃ u ∈ d.Q, ∃ w ∈ K.c.W, x = u * w := by
  refine ⟨fun hx => exists_mul_of_mem_sup_of_le_centralizer K.Q_le_centralizer_W hx, ?_⟩
  rintro ⟨u, hu, w, hw, rfl⟩
  exact mul_mem (mem_sup_left hu) (mem_sup_right hw)

theorem W_le_S : K.c.W ≤ d.S := fun _ hw => hw.1

theorem qwSub_le_QS : qwSub K.c ≤ d.QS :=
  sup_le_sup le_rfl (K.W_le_S)

theorem qwSub_le_X : qwSub K.c ≤ d.X := K.qwSub_le_QS.trans d.QS_le_X

theorem qwSub_le_centralizer_V : qwSub K.c ≤ centralizer (K.c.V : Set G) := by
  refine sup_le (fun u hu => ?_) (fun w hw => ?_)
  · rw [mem_centralizer_iff]
    intro v hv
    exact d.comm_Q_S hu (K.c.V_le_S K.h hv)
  · rw [mem_centralizer_iff]
    intro v hv
    exact K.c.W_comm_V hw hv |>.symm

theorem graph_mem_centralizer_V {y : G} (hy : K.c.rep Kind.graph = some y) :
    y ∈ centralizer (K.c.V : Set G) := by
  obtain ⟨-, -, hact⟩ := K.c.rep_mem Kind.graph y hy
  rw [mem_centralizer_iff]
  intro v hv
  have := K.c.graph_fixes_V K.hα K.h K.hP K.hQ hact v hv
  calc v * y = y * (y⁻¹ * v * y) := by group
    _ = y * v := by rw [this]

end Cfg

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem centralizer_V_cases {x : G} (hx : x ∈ d.X ⊓ centralizer (K.c.V : Set G)) :
    x ∈ qwSub K.c ∨ ∃ y, K.c.rep Kind.graph = some y ∧ ∃ b ∈ qwSub K.c, x = b * y := by
  rcases K.c.centralizing_V K.hα K.h K.hP K.hQ K.hS2 hx.1
    (fun v hv => (mem_centralizer_iff.1 hx.2 v hv).symm) with
    ⟨u, hu, s, hs, rfl⟩ | ⟨y, hy, u, hu, s, hs, rfl⟩
  · left
    exact K.mem_qwSub_iff.2 ⟨u, hu, s, hs, rfl⟩
  · right
    exact ⟨y, hy, u * s, K.mem_qwSub_iff.2 ⟨u, hu, s, hs, rfl⟩, rfl⟩

theorem qw_relIndex_two :
    (qwSub K.c).relIndex (d.X ⊓ centralizer (K.c.V : Set G)) = 2 := by
  obtain ⟨y, hy⟩ := K.exists_rep Kind.graph
  obtain ⟨hyX, hyQS, hact⟩ := K.c.rep_mem Kind.graph y hy
  have hyP : y ∈ d.X ⊓ centralizer (K.c.V : Set G) := ⟨hyX, K.graph_mem_centralizer_V hy⟩
  have hy2 : y * y ∈ qwSub K.c := mem_sup_left (K.c.sq_mem_Q K.hα K.h K.hP K.hQ Kind.graph hyX hact)
  have hBQS := K.qwSub_le_QS
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨y, hyP⟩, fun b => ?_⟩
  by_cases hb : (b : G) ∈ qwSub K.c
  · right
    refine ⟨mem_subgroupOf.2 hb, fun hby => ?_⟩
    have hby' : (b : G) * y ∈ qwSub K.c := mem_subgroupOf.1 hby
    apply hyQS
    have : y = (b : G)⁻¹ * ((b : G) * y) := by group
    rw [this]
    exact hBQS (mul_mem (inv_mem hb) hby')
  · left
    refine ⟨?_, fun hb' => hb (mem_subgroupOf.1 hb')⟩
    rcases K.centralizer_V_cases b.2 with h1 | ⟨y', hy', b', hb', hbe⟩
    · exact absurd h1 hb
    · rw [hy] at hy'
      have hyy : y' = y := (Option.some_injective _ hy').symm
      rw [hyy] at hbe
      apply mem_subgroupOf.2
      show (b : G) * y ∈ qwSub K.c
      rw [hbe, mul_assoc]
      exact mul_mem hb' hy2

theorem t_mem_centralizer_V :
    K.c.t ∈ centralizer (K.c.V : Set G) :=
  K.qwSub_le_centralizer_V (mem_sup_right (K.c.t_mem_W K.h K.hP K.hQ K.hα))

theorem comm_t_of_mem_qwSub {b : G} (hb : b ∈ qwSub K.c) : b * K.c.t = K.c.t * b := by
  obtain ⟨u, hu, w, hw, rfl⟩ := K.mem_qwSub_iff.1 hb
  have h1 : u * K.c.t = K.c.t * u := K.Q_comm hu K.c.t_mem.1
  have h2 : w * K.c.t = K.c.t * w := K.t_comm hw.1
  calc u * w * K.c.t = u * (w * K.c.t) := by group
    _ = u * (K.c.t * w) := by rw [h2]
    _ = (u * K.c.t) * w := by group
    _ = (K.c.t * u) * w := by rw [h1]
    _ = K.c.t * (u * w) := by group

theorem isSylowOf_P :
    CFSG.ABGLocalTools.IsSylowOf 2 (d.X ⊓ centralizer (K.c.V : Set G))
      (centralizer (K.c.V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : d.X ≤ normalizer (K.c.V : Set G) := fun _ hx =>
    mem_normalizer_iff.2 fun v => (K.c.X_normalizes K.hα K.h K.hP K.hQ K.hS2 K.hc hx).2 v
  have hNC : normalizer (K.c.V : Set G) ≤
      normalizer ((centralizer (K.c.V : Set G) : Subgroup G) : Set G) := fun h hh =>
    mem_normalizer_fintype fun x hx =>
      conj_mem_centralizer_of_normalizer (fun v => mem_normalizer_iff.1 hh v) hx
  exact ((K.c.X_sylow_G_of_facts K.hα K.h K.hP K.hQ).of_le hXN le_top).inf_of_le_normalizer
    (centralizer_le_normalizer _) hNC

theorem exists_mul_mem_normalizer_P {h : G} (hh : h ∈ normalizer (K.c.V : Set G)) :
    ∃ c ∈ centralizer (K.c.V : Set G), c⁻¹ * h ∈ normalizer (K.c.V : Set G) ∧
      c⁻¹ * h ∈ normalizer ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hch⟩ := exists_mul_mem_normalizer_of_isSylowOf K.isSylowOf_P
    (fun x hx => conj_mem_centralizer_of_normalizer (fun v => mem_normalizer_iff.1 hh v) hx)
  exact ⟨c, hc, mul_mem (inv_mem ((centralizer_le_normalizer _) hc)) hh, hch⟩

end Cfg

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem qwSub_comm {x x' : G} (hx : x ∈ qwSub K.c) (hx' : x' ∈ qwSub K.c) :
    x * x' = x' * x := by
  obtain ⟨u, hu, w, hw, rfl⟩ := K.mem_qwSub_iff.1 hx
  obtain ⟨u', hu', w', hw', rfl⟩ := K.mem_qwSub_iff.1 hx'
  have hW : ∀ a ∈ K.c.W, ∀ b ∈ K.c.W, a * b = b * a := (K.sf.W_comm_iff).2 rfl
  have h1 : w * u' = u' * w := d.comm_Q_S hu' hw.1
  have h2 : w' * u = u * w' := d.comm_Q_S hu hw'.1
  have h3 : u * u' = u' * u := K.Q_comm hu hu'
  have h4 : w * w' = w' * w := hW w hw w' hw'
  calc u * w * (u' * w') = u * (w * u') * w' := by group
    _ = u * (u' * w) * w' := by rw [h1]
    _ = (u * u') * (w * w') := by group
    _ = (u' * u) * (w' * w) := by rw [h3, h4]
    _ = u' * (u * w') * w := by group
    _ = u' * (w' * u) * w := by rw [← h2]
    _ = u' * w' * (u * w) := by group

theorem mem_qwSub_of_central {x : G}
    (hx : x ∈ d.X ⊓ centralizer (K.c.V : Set G))
    (hz : ∀ p ∈ d.X ⊓ centralizer (K.c.V : Set G), x * p = p * x) : x ∈ qwSub K.c := by
  rcases K.centralizer_V_cases hx with h | ⟨y, hy, b, hb, rfl⟩
  · exact h
  · exfalso
    obtain ⟨-, -, hact⟩ := K.c.rep_mem Kind.graph y hy
    have hzt : cj K.c.t y = K.c.t⁻¹ := by
      simp only [Kind.Act, ↓reduceIte] at hact
      exact hact.1
    have h1 := hz K.c.t ⟨d.S_le_X K.c.t_mem.2, K.t_mem_centralizer_V⟩
    have h2 : cj K.c.t (b * y) = K.c.t := by
      unfold cj
      calc (b * y)⁻¹ * K.c.t * (b * y) = (b * y)⁻¹ * (K.c.t * (b * y)) := by group
        _ = (b * y)⁻¹ * ((b * y) * K.c.t) := by rw [h1]
        _ = K.c.t := by group
    have h3 : cj K.c.t (b * y) = K.c.t⁻¹ := by
      rw [← cj_cj]
      have : cj K.c.t b = K.c.t := cj_of_commute (K.comm_t_of_mem_qwSub hb).symm
      rw [this, hzt]
    exact K.c.shape_t_inv_ne (h3.symm.trans h2)

theorem sq_eq_one_of_comm_graph
    {y x : G} (hy : K.c.rep Kind.graph = some y) (hx : x ∈ qwSub K.c) (hxy : x * y = y * x) :
    x * x = 1 := by
  by_contra hne
  obtain ⟨hyX, hyQS, hact⟩ := K.c.rep_mem Kind.graph y hy
  have hzt : cj K.c.t y = K.c.t⁻¹ := by
    simp only [Kind.Act, ↓reduceIte] at hact
    exact hact.1
  have hxX : x ∈ d.X := K.qwSub_le_X hx
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 d.X_sylow.isPGroup) ⟨x, hxX⟩
  have hj' : orderOf x = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hne
    have hdvd : orderOf x ∣ 2 := by
      rw [hj']
      exact (Nat.pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by norm_num)
    have : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
    simpa [pow_two] using this
  set c₀ := x ^ 2 ^ (j - 2) with hc₀
  have hord : orderOf c₀ = 4 := by
    rw [hc₀, orderOf_pow_of_dvd (by positivity)
      (by rw [hj']; exact Nat.pow_dvd_pow 2 (by omega)), hj', Nat.pow_div (by omega) (by norm_num)]
    have : j - (j - 2) = 2 := by omega
    rw [this]
  have hc₀B : c₀ ∈ qwSub K.c := pow_mem hx _
  have hc₀y : c₀ * y = y * c₀ := ((Commute.pow_left (show Commute x y from hxy) _)).eq
  have hc₀4 : c₀ ^ 4 = 1 := by
    have := pow_orderOf_eq_one c₀
    rwa [hord] at this
  obtain ⟨u', hu', w', hw', hcu⟩ := K.mem_qwSub_iff.1 hc₀B
  have hcomm : Commute u' w' := (d.comm_Q_S hu' hw'.1).symm
  have hw4 : w' ^ 4 = 1 := K.c.W_pow_four K.hα K.h K.hP K.hQ w' hw'
  have hu4 : u' ^ 4 = 1 := by
    have h1 : c₀ ^ 4 = u' ^ 4 * w' ^ 4 := by rw [hcu]; exact hcomm.mul_pow 4
    rw [hc₀4, hw4, mul_one] at h1
    exact h1.symm
  have hu'W : u' ∈ K.c.W :=
    (Subgroup.zpowers_le.2 (K.c.t_mem_W K.h K.hP K.hQ K.hα))
      (K.c.mem_zpowers_t_of_pow_four K.h hu' hu4)
  have hc₀W : c₀ ∈ K.c.W := by rw [hcu]; exact mul_mem hu'W hw'
  have hcj : cj c₀ y = c₀ := by
    unfold cj
    calc y⁻¹ * c₀ * y = y⁻¹ * (c₀ * y) := by group
      _ = y⁻¹ * (y * c₀) := by rw [hc₀y]
      _ = c₀ := by group
  have hc₀V : c₀ ∈ K.c.V :=
    (K.c.centralizer_graph_eq_V K.hα K.h K.hP K.hQ hyX hact hzt c₀ hc₀W.1).1 hcj
  have h2 : c₀ ^ 2 = 1 := by rw [pow_two]; exact K.sf.V_sq c₀ hc₀V
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at this
  omega

theorem central_le_V {x : G}
    (hx : x ∈ d.X ⊓ centralizer (K.c.V : Set G))
    (hz : ∀ p ∈ d.X ⊓ centralizer (K.c.V : Set G), x * p = p * x) : x ∈ K.c.V := by
  have hxB := K.mem_qwSub_of_central hx hz
  obtain ⟨y, hy⟩ := K.exists_rep Kind.graph
  have hxy : x * y = y * x :=
    hz y ⟨(K.c.rep_mem Kind.graph y hy).1, K.graph_mem_centralizer_V hy⟩
  have hx2 := K.sq_eq_one_of_comm_graph hy hxB hxy
  have hxS : x ∈ d.S :=
    K.c.involutions_in_S' K.hα K.h K.hP K.hQ K.hc (K.qwSub_le_QS hxB) hx2
  have hxW : x ∈ K.c.W :=
    K.c.mem_W_of_comm hxS (fun v hv => (mem_centralizer_iff.1 hx.2 v hv).symm)
  exact K.sf.W_invol x hxW hx2

theorem Q_le_zpowers_t
    (hqπ : IsConj d.q K.c.pi) : ∀ u ∈ d.Q, u ∈ zpowers K.c.t := by
  obtain ⟨n, hnN, hn⟩ := K.c.fuse_in_normalizer' K.hα K.h K.hP K.hQ K.hS2 K.hc hqπ
  obtain ⟨c, hcC, -, hmP⟩ := K.exists_mul_mem_normalizer_P (inv_mem hnN)
  set m := c⁻¹ * n⁻¹ with hmdef
  have hpiV : K.c.pi ∈ K.c.V := subset_closure (by simp)
  have hmq : m * d.q * m⁻¹ = K.c.pi := by
    have h1 : n⁻¹ * d.q * n⁻¹⁻¹ = K.c.pi := by rw [← hn]; simp [cj]
    have h2 : K.c.pi * c = c * K.c.pi := mem_centralizer_iff.1 hcC K.c.pi hpiV
    calc m * d.q * m⁻¹ = c⁻¹ * (n⁻¹ * d.q * n⁻¹⁻¹) * c := by rw [hmdef]; group
      _ = c⁻¹ * (K.c.pi * c) := by rw [h1, mul_assoc]
      _ = K.c.pi := by rw [h2]; group
  set P : Subgroup G := d.X ⊓ centralizer (K.c.V : Set G) with hP
  set B : Subgroup G := qwSub K.c with hB
  set B' : Subgroup G := B.map (MulAut.conj m).toMonoidHom with hB'
  have hBP : B ≤ P := le_inf K.qwSub_le_X K.qwSub_le_centralizer_V
  have hPm : P.map (MulAut.conj m).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.1 hmP
  have hB'P : B' ≤ P := hPm ▸ Subgroup.map_mono hBP
  have hBi : B.relIndex P = 2 := K.qw_relIndex_two
  have hB'i : B'.relIndex P = 2 := by
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj m).toMonoidHom) B P
      (MulAut.conj m).injective
    rw [hPm] at this
    rw [this]
    exact hBi
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => K.qwSub_comm hx hy
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩
    have := K.qwSub_comm hb₁ hb₂
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m * b₁ * m⁻¹ * (m * b₂ * m⁻¹) = m * (b₁ * b₂) * m⁻¹ := by group
      _ = m * (b₂ * b₁) * m⁻¹ := by rw [this]
      _ = m * b₂ * m⁻¹ * (m * b₁ * m⁻¹) := by group
  have hB64 : 64 ≤ Nat.card B := by
    have : Nat.card K.c.W ≤ Nat.card B := Subgroup.card_le_of_le (le_sup_right : K.c.W ≤ B)
    rw [K.sf.card_W] at this
    exact this
  have hZ : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ K.c.V := fun x hx hz =>
    K.central_le_V hx hz
  have hB'B : B' = B := eq_of_abelian_relIndex_two hBP hB'P hBi hB'i hBab hB'ab hB64
    K.sf.card_V hZ
  intro u hu
  by_contra hut
  have hu4 : u ^ 4 ≠ 1 := fun h => hut (K.c.mem_zpowers_t_of_pow_four K.h hu h)
  have huX : u ∈ d.X := d.Q_le_X hu
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 d.X_sylow.isPGroup) ⟨u, huX⟩
  have hj' : orderOf u = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hj3 : 3 ≤ j := by
    by_contra hlt
    apply hu4
    have hdvd : orderOf u ∣ 4 := by
      rw [hj']
      exact (Nat.pow_dvd_pow 2 (by omega : j ≤ 2))
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  set u₀ := u ^ 2 ^ (j - 3) with hu₀
  have hord8 : orderOf u₀ = 8 := by
    rw [hu₀, orderOf_pow_of_dvd (by positivity)
      (by rw [hj']; exact Nat.pow_dvd_pow 2 (by omega)), hj', Nat.pow_div (by omega) (by norm_num)]
    have : j - (j - 3) = 3 := by omega
    rw [this]
  have hu₀Q : u₀ ∈ d.Q := pow_mem hu _
  have hord2 : orderOf (u₀ ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord8]; norm_num), hord8]
  have hqu : u₀ ^ 4 = d.q := by
    have hcyc : IsCyclic d.Q := d.Q_isCyclic K.h
    exact eq_of_orderOf_two_of_isCyclic hcyc (pow_mem hu₀Q 4) (d.q_mem_Q K.h) hord2 d.q_ord
  have hu₀B : u₀ ∈ B := mem_sup_left hu₀Q
  have hb₁ : m * u₀ * m⁻¹ ∈ B := hB'B ▸ ⟨u₀, hu₀B, rfl⟩
  obtain ⟨u₁, hu₁, w₁, hw₁, hbe⟩ := K.mem_qwSub_iff.1 hb₁
  have hw4 : w₁ ^ 4 = 1 := K.c.W_pow_four K.hα K.h K.hP K.hQ w₁ hw₁
  have hcomm : Commute u₁ w₁ := (d.comm_Q_S hu₁ hw₁.1).symm
  have hπ4 : K.c.pi = u₁ ^ 4 := by
    have h1 : m * d.q * m⁻¹ = (m * u₀ * m⁻¹) ^ 4 := by
      rw [← hqu]
      simp only [← MulAut.conj_apply]
      rw [map_pow]
    rw [← hmq, h1, hbe, hcomm.mul_pow, hw4, mul_one]
  have hπQ : K.c.pi ∈ d.Q := by
    rw [hπ4]
    exact pow_mem hu₁ 4
  have hπt : K.c.pi ∈ zpowers K.c.t := by
    rw [← K.c.Q_inf_S_eq K.hc]
    exact ⟨hπQ, K.c.mem.1⟩
  exact K.c.shape_pi_not_mem_zpowers hπt

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
