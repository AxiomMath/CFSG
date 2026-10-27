module

public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG
open scoped commutatorElement

section AbelianByTwo

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]

omit [N.Normal] in
theorem mem_or_of_index_two (hidx : N.index = 2) {t : G} (ht : t ∉ N) (g : G) :
    g ∈ N ∨ t⁻¹ * g ∈ N := by
  by_cases hg : g ∈ N
  · exact Or.inl hg
  · right
    have h1 : t⁻¹ ∉ N := fun h => ht (by simpa using N.inv_mem h)
    exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false h1 hg)

omit [N.Normal] in
theorem sq_mem_of_index_two (hidx : N.index = 2) {t : G} (ht : t ∉ N) : t * t ∈ N :=
  (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false ht ht)

def commSubgroup (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (t : G) : Subgroup G where
  carrier := {w | ∃ n ∈ N, w = n * t * n⁻¹ * t⁻¹}
  one_mem' := ⟨1, N.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, rfl⟩ ⟨n₂, hn₂, rfl⟩
    refine ⟨n₁ * n₂, N.mul_mem hn₁ hn₂, ?_⟩
    have h1 : t * n₁⁻¹ * t⁻¹ ∈ N := by
      have := Normal.conj_mem (inferInstance : N.Normal) _ (N.inv_mem hn₁) t
      exact this
    have h2 := hab n₂ hn₂ (t * n₁⁻¹ * t⁻¹) h1
    calc n₁ * t * n₁⁻¹ * t⁻¹ * (n₂ * t * n₂⁻¹ * t⁻¹)
        = n₁ * ((t * n₁⁻¹ * t⁻¹) * n₂) * t * n₂⁻¹ * t⁻¹ := by group
      _ = n₁ * (n₂ * (t * n₁⁻¹ * t⁻¹)) * t * n₂⁻¹ * t⁻¹ := by rw [h2]
      _ = n₁ * n₂ * t * (n₂ * n₁)⁻¹ * t⁻¹ := by group
      _ = n₁ * n₂ * t * (n₁ * n₂)⁻¹ * t⁻¹ := by rw [hab n₂ hn₂ n₁ hn₁]
  inv_mem' := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
    have h1 : t * n⁻¹ * t⁻¹ ∈ N := by
      have := Normal.conj_mem (inferInstance : N.Normal) _ (N.inv_mem hn) t
      exact this
    have h2 := hab n hn (t * n⁻¹ * t⁻¹) h1
    calc (n * t * n⁻¹ * t⁻¹)⁻¹ = t * n * t⁻¹ * n⁻¹ := by group
      _ = n⁻¹ * (n * (t * n * t⁻¹)) * n⁻¹ := by group
      _ = n⁻¹ * ((t * n * t⁻¹) * n) * n⁻¹ := by
        have h3 : t * n * t⁻¹ ∈ N := Normal.conj_mem (inferInstance : N.Normal) _ hn t
        rw [hab n hn _ h3]
      _ = n⁻¹ * t * n⁻¹⁻¹ * t⁻¹ := by group

theorem comm_mem_commSubgroup (hidx : N.index = 2) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {t : G}
    (ht : t ∉ N) (x y : G) : ⁅x, y⁆ ∈ commSubgroup hab t := by
  have case2 : ∀ x y : G, x ∈ N → y ∉ N → ⁅x, y⁆ ∈ commSubgroup hab t := by
    intro x y hx hy
    have hm : t⁻¹ * y ∈ N := by
      rcases mem_or_of_index_two hidx ht y with h | h
      · exact absurd h hy
      · exact h
    refine ⟨x, hx, ?_⟩
    have h1 := hab (t⁻¹ * y) hm x⁻¹ (N.inv_mem hx)
    calc ⁅x, y⁆ = x * (t * (t⁻¹ * y)) * x⁻¹ * (t * (t⁻¹ * y))⁻¹ := by
          rw [commutatorElement_def]; group
      _ = x * t * ((t⁻¹ * y) * x⁻¹ * (t⁻¹ * y)⁻¹) * t⁻¹ := by group
      _ = x * t * x⁻¹ * t⁻¹ := by
        have h2 : (t⁻¹ * y) * x⁻¹ * (t⁻¹ * y)⁻¹ = x⁻¹ := by rw [h1]; group
        rw [h2]
  by_cases hx : x ∈ N <;> by_cases hy : y ∈ N
  ·
    have : ⁅x, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]; exact hab x hx y hy
    rw [this]; exact (commSubgroup hab t).one_mem
  · exact case2 x y hx hy
  · have := (commSubgroup hab t).inv_mem (case2 y x hy hx)
    rwa [commutatorElement_inv] at this
  ·
    have hu : y * x⁻¹ ∈ N := by
      have hx' : x⁻¹ ∉ N := fun h => hx (by simpa using N.inv_mem h)
      exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hy hx')
    have e : ⁅x, y⁆ = ⁅x, y * x⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [e]
    have := (commSubgroup hab t).inv_mem (case2 (y * x⁻¹) x hu hx)
    rwa [commutatorElement_inv] at this

theorem commutator_le_commSubgroup (hidx : N.index = 2) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {t : G} (ht : t ∉ N) : commutator G ≤ commSubgroup hab t := by
  rw [commutator_def]
  exact Subgroup.commutator_le.mpr fun x _ y _ => comm_mem_commSubgroup hidx hab ht x y

theorem commF_mul (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (t : G) {n₁ n₂ : G} (hn₁ : n₁ ∈ N)
    (hn₂ : n₂ ∈ N) :
    (n₁ * n₂) * t * (n₁ * n₂)⁻¹ * t⁻¹ = (n₁ * t * n₁⁻¹ * t⁻¹) * (n₂ * t * n₂⁻¹ * t⁻¹) := by
  have h1 : t * n₁⁻¹ * t⁻¹ ∈ N := Normal.conj_mem (inferInstance : N.Normal) _ (N.inv_mem hn₁) t
  have h2 := hab n₂ hn₂ (t * n₁⁻¹ * t⁻¹) h1
  calc (n₁ * n₂) * t * (n₁ * n₂)⁻¹ * t⁻¹ = n₁ * n₂ * t * (n₂ * n₁)⁻¹ * t⁻¹ := by
        rw [hab n₁ hn₁ n₂ hn₂]
    _ = n₁ * (n₂ * (t * n₁⁻¹ * t⁻¹)) * t * n₂⁻¹ * t⁻¹ := by group
    _ = n₁ * ((t * n₁⁻¹ * t⁻¹) * n₂) * t * n₂⁻¹ * t⁻¹ := by rw [h2]
    _ = (n₁ * t * n₁⁻¹ * t⁻¹) * (n₂ * t * n₂⁻¹ * t⁻¹) := by group

theorem commF_pow (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (t : G) {n : G} (hn : n ∈ N) (j : ℕ) :
    n ^ j * t * (n ^ j)⁻¹ * t⁻¹ = (n * t * n⁻¹ * t⁻¹) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, commF_mul hab t (N.pow_mem hn j) hn, ih]

theorem exists_two_part [Finite G] (hidx : N.index = 2) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {t : G} (ht : t ∉ N) {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤)
    {w : G} (hw : w ∈ commutator G) (hw2 : w * w = 1) :
    ∃ n ∈ S ⊓ N, w = n * t * n⁻¹ * t⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hwn⟩ := commutator_le_commSubgroup hidx hab ht hw
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card N) Nat.card_pos.ne'
  have hwm : w ^ m = w := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hw2, one_pow, one_mul]
  have hw' : w = n ^ m * t * (n ^ m)⁻¹ * t⁻¹ := by
    rw [commF_pow hab t hn m, ← hwn, hwm]
  have hn'N : n ^ m ∈ N := N.pow_mem hn m
  have hn'2 : (n ^ m) ^ 2 ^ k = 1 := by
    have h1 : (⟨n, hn⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 : n ^ Nat.card N = 1 :=
      (Subgroup.coe_pow N ⟨n, hn⟩ (Nat.card N)).symm.trans (congrArg Subtype.val h1)
    rw [← pow_mul, mul_comm, ← hcard]
    exact h2
  refine ⟨n ^ m, ?_, hw'⟩
  refine ⟨?_, hn'N⟩
  have hSN : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ N) N :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hS le_top (by
      intro g _
      exact Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => Normal.conj_mem inferInstance h hh g,
        fun hh => by
          have := Normal.conj_mem (inferInstance : N.Normal) _ hh g⁻¹
          simpa [mul_assoc] using this⟩)
  obtain ⟨Q, hQ⟩ := hSN.exists_sylow_eq_subgroupOf
  have hnorm : (⟨n ^ m, hn'N⟩ : N) ∈ Subgroup.normalizer ((Q : Subgroup N) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have : (⟨n ^ m, hn'N⟩ : N) * h * (⟨n ^ m, hn'N⟩ : N)⁻¹ = h := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hab _ hn'N _ h.2]; group
    rw [this]
  have hmem := CFSG.Walter.J1.JankoHyp.mem_sylow_of_mem_normalizer Q hnorm
    (k := k) (Subtype.ext (by simpa using hn'2))
  have hmem' : (⟨n ^ m, hn'N⟩ : N) ∈ (Q : Subgroup N) := hmem
  rw [hQ, Subgroup.mem_subgroupOf] at hmem'
  exact hmem'.1

end AbelianByTwo

section CaH

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H} {T : Subgroup H} {a : H}

omit [Finite H] in
theorem comm_of_conj_eq {c y : H} (h : c * y * c⁻¹ = y) : y * c = c * y :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

theorem Setting.comm_mem (hS : Setting H K₁ K₂ z) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) {u v : H}
    (hu : u ∈ normalizer (K₁ : Set H)) (hv : v ∈ normalizer (K₁ : Set H)) :
    ⁅u, v⁆ ∈ K₁ ⊔ K₂ := by
  obtain ⟨k₁, hk₁, h1⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.exists_inner_commutator
    (MulEquiv.refl ↥K₁) (out_abelian_of_type h2A7 hS.type₁) hu hv
  obtain ⟨k₂, hk₂, h2⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.exists_inner_commutator
    (MulEquiv.refl ↥K₂) (out_abelian_of_type h2A7 hS.type₂) (hS.normalizer₁₂ hu) (hS.normalizer₁₂ hv)
  have hc : (k₁ * k₂)⁻¹ * ⁅u, v⁆ ∈ centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) := by
    have hle : K₁ ⊔ K₂ ≤ centralizer ({(k₁ * k₂)⁻¹ * ⁅u, v⁆} : Set H) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hy1 := h1 y hy
        apply comm_of_conj_eq
        calc (k₁ * k₂)⁻¹ * ⁅u, v⁆ * y * ((k₁ * k₂)⁻¹ * ⁅u, v⁆)⁻¹
            = (k₁ * k₂)⁻¹ * (⁅u, v⁆ * y * ⁅u, v⁆⁻¹) * (k₁ * k₂) := by group
          _ = (k₁ * k₂)⁻¹ * (k₁ * y * k₁⁻¹) * (k₁ * k₂) := by rw [hy1]
          _ = k₂⁻¹ * y * k₂ := by group
          _ = y := by
            have h3 := hS.comm y hy k₂⁻¹ (K₂.inv_mem hk₂)
            rw [← h3]; group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hy2 := h2 y hy
        apply comm_of_conj_eq
        calc (k₁ * k₂)⁻¹ * ⁅u, v⁆ * y * ((k₁ * k₂)⁻¹ * ⁅u, v⁆)⁻¹
            = (k₁ * k₂)⁻¹ * (⁅u, v⁆ * y * ⁅u, v⁆⁻¹) * (k₁ * k₂) := by group
          _ = (k₁ * k₂)⁻¹ * (k₂ * y * k₂⁻¹) * (k₁ * k₂) := by rw [hy2]
          _ = k₁⁻¹ * y * k₁ := by
            have hk12 : k₁ * k₂ = k₂ * k₁ := hS.comm k₁ hk₁ k₂ hk₂
            have hk21 : k₂⁻¹ * k₁ * k₂ = k₁ := by
              calc k₂⁻¹ * k₁ * k₂ = k₂⁻¹ * (k₁ * k₂) := by group
                _ = k₁ := by rw [hk12]; group
            calc (k₁ * k₂)⁻¹ * (k₂ * y * k₂⁻¹) * (k₁ * k₂)
                = k₁⁻¹ * (k₂⁻¹ * (k₂ * y * k₂⁻¹) * (k₁ * k₂)) := by
                  rw [show (k₁ * k₂)⁻¹ = k₁⁻¹ * k₂⁻¹ by rw [hk12]; group]; group
              _ = k₁⁻¹ * (y * (k₂⁻¹ * k₁ * k₂)) := by group
              _ = k₁⁻¹ * y * k₁ := by rw [hk21]; group
          _ = y := by
            have h3 := hS.comm k₁⁻¹ (K₁.inv_mem hk₁) y hy
            calc k₁⁻¹ * y * k₁ = y * k₁⁻¹ * k₁ := by rw [h3]
              _ = y := by group
    exact Subgroup.mem_centralizer_iff.mpr fun m hm => by
      have := hle hm
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
  have hK := hS.centralizer_le hc
  have : ⁅u, v⁆ = (k₁ * k₂) * ((k₁ * k₂)⁻¹ * ⁅u, v⁆) := by group
  rw [this]
  exact (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left hk₁) (Subgroup.mem_sup_right hk₂)) hK

theorem Hyp.T1_lt (h : Hyp H K₁ K₂ z T a) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) : T1 T K₁ < T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  refine lt_of_le_of_ne inf_le_left fun hEq => ?_
  have hTN : T ≤ normalizer (K₁ : Set H) := fun x hx => by
    have : x ∈ T1 T K₁ := by rw [hEq]; exact hx
    exact this.2
  have hdvd : (normalizer (K₁ : Set H)).index ∣ T.index := Subgroup.index_dvd_of_le hTN
  obtain ⟨-, -, hodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow
  rw [Subgroup.relIndex_top_right] at hodd
  have hle := hS.index_le_two
  have hpos : (normalizer (K₁ : Set H)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (normalizer (K₁ : Set H)).index = 1 := by
    by_contra hne
    have : (normalizer (K₁ : Set H)).index = 2 := by omega
    rw [this] at hdvd
    exact hodd hdvd
  have htop : normalizer (K₁ : Set H) = ⊤ := Subgroup.index_eq_one.mp h1
  have hcomm : commutator H ≤ K₁ ⊔ K₂ := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun u _ v _ =>
      hS.comm_mem h2A7 (by rw [htop]; trivial) (by rw [htop]; trivial)
  exact h.a_not_mem_K (hcomm h.a_comm)

theorem Hyp.exists_comm_rep (h : Hyp H K₁ K₂ z T a) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) {t : H}
    (htT : t ∈ T) (htN : t ∉ normalizer (K₁ : Set H)) :
    ∃ h' ∈ T1 T K₁, a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) ∈ P T K₁ K₂ ∧ (t * a * t⁻¹) * a ∈ K₁ ⊔ K₂ ∧
      (t⁻¹ * a * t) * a ∈ K₁ ⊔ K₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.setting
  have hKn : (K₁ ⊔ K₂).Normal := hS.normal
  set N := normalizer (K₁ : Set H) with hNdef
  have hKN : K₁ ⊔ K₂ ≤ N := sup_le Subgroup.le_normalizer hS.le_normalizer₁
  have hidx : N.index = 2 := by
    have hle : N.index ≤ 2 := hS.index_le_two
    have hne : N.index ≠ 1 := fun h1 => htN (by rw [Subgroup.index_eq_one.mp h1]; trivial)
    have hpos : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hNnorm : N.Normal := Subgroup.normal_of_index_eq_two hidx
  let π : H →* H ⧸ (K₁ ⊔ K₂) := QuotientGroup.mk' _
  have hker : π.ker = K₁ ⊔ K₂ := QuotientGroup.ker_mk' _
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmemN : ∀ x : H, π x ∈ N.map π → x ∈ N := by
    rintro x ⟨u, hu, hux⟩
    have h1 : u⁻¹ * x ∈ K₁ ⊔ K₂ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
    have h2 : u⁻¹ * x ∈ N := hKN h1
    have := N.mul_mem hu h2
    simpa using this
  have hNb : (N.map π).Normal := Subgroup.Normal.map hNnorm π hsurj
  have hNbidx : (N.map π).index = 2 :=
    (Subgroup.index_map_eq N hsurj (by rw [hker]; exact hKN)).trans hidx
  have hNbab : ∀ x ∈ N.map π, ∀ y ∈ N.map π, x * y = y * x := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul]
    have h1 : (u * v)⁻¹ * (v * u) ∈ K₁ ⊔ K₂ := by
      have := hS.comm_mem h2A7 (N.inv_mem hv) (N.inv_mem hu)
      convert this using 1
      simp [commutatorElement_def, mul_assoc]
    exact QuotientGroup.eq.mpr h1
  have htb : π t ∉ N.map π := fun hh => htN (hmemN t hh)
  have hSb : CFSG.ABGLocalTools.IsSylowOf 2 (T.map π) ⊤ := by
    have hsyl := h.sylow
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl ⊢
    obtain ⟨-, hTp, hodd⟩ := hsyl
    refine ⟨le_top, hTp.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    rw [Subgroup.relIndex_top_right] at hodd
    exact fun hd => hodd (hd.trans (Subgroup.index_map_dvd T hsurj))
  have hw : π a ∈ commutator (H ⧸ (K₁ ⊔ K₂)) := by
    have h1 : (commutator H).map π ≤ commutator (H ⧸ (K₁ ⊔ K₂)) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h1 (Subgroup.mem_map.2 ⟨a, h.a_comm, rfl⟩)
  have hw2 : π a * π a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := by
      have := pow_orderOf_eq_one a
      rwa [h.a_ord, sq] at this
    rw [this, map_one]
  obtain ⟨n, ⟨hnS, hnN⟩, hn⟩ := exists_two_part (N := N.map π) hNbidx hNbab htb hSb hw hw2
  obtain ⟨h', hh'T, rfl⟩ := Subgroup.mem_map.1 hnS
  have hh'N : h' ∈ N := hmemN h' hnN
  refine ⟨h', ⟨hh'T, hh'N⟩, ?_⟩
  have hq : a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) ∈ K₁ ⊔ K₂ := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hn]
    simp only [map_mul, map_inv]
    group
  have htt : π (t * t) ∈ N.map π := Subgroup.mem_map.2 ⟨t * t, sq_mem_of_index_two hidx htN, rfl⟩
  have hc := hNbab (π h') hnN (π (t * t)) htt
  rw [map_mul] at hc
  have hc' : (π h')⁻¹ * ((π t)⁻¹ * (π t)⁻¹) * π h' = (π t)⁻¹ * (π t)⁻¹ := by
    have h1 : (π t)⁻¹ * (π t)⁻¹ * π h' = π h' * ((π t)⁻¹ * (π t)⁻¹) := by
      have h2 : π h' * (π t * π t) = (π t * π t) * π h' := hc
      calc (π t)⁻¹ * (π t)⁻¹ * π h' = ((π t * π t)⁻¹) * π h' := by group
        _ = ((π t * π t)⁻¹ * (π h' * (π t * π t))) * (π t * π t)⁻¹ := by group
        _ = ((π t * π t)⁻¹ * ((π t * π t) * π h')) * (π t * π t)⁻¹ := by rw [h2]
        _ = π h' * ((π t)⁻¹ * (π t)⁻¹) := by group
    calc (π h')⁻¹ * ((π t)⁻¹ * (π t)⁻¹) * π h' = (π h')⁻¹ * ((π t)⁻¹ * (π t)⁻¹ * π h') := by group
      _ = (π t)⁻¹ * (π t)⁻¹ := by rw [h1]; group
  have hc'' : (π h') * ((π t) * (π t)) * (π h')⁻¹ = (π t) * (π t) := by
    have h2 : π h' * (π t * π t) = (π t * π t) * π h' := hc
    rw [h2]; group
  have hPmem : a⁻¹ * (h' * t * h'⁻¹ * t⁻¹) ∈ P T K₁ K₂ := by
    refine ⟨T.mul_mem (T.inv_mem h.a_mem.1) ?_, hq⟩
    exact T.mul_mem (T.mul_mem (T.mul_mem hh'T htT) (T.inv_mem hh'T)) (T.inv_mem htT)
  refine ⟨hPmem, ?_, ?_⟩
  · rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hn]
    calc π t * (π h' * π t * (π h')⁻¹ * (π t)⁻¹) * (π t)⁻¹ * (π h' * π t * (π h')⁻¹ * (π t)⁻¹)
        = π t * π h' * π t * ((π h')⁻¹ * ((π t)⁻¹ * (π t)⁻¹) * π h') * π t * (π h')⁻¹ * (π t)⁻¹ := by
          group
      _ = π t * π h' * π t * ((π t)⁻¹ * (π t)⁻¹) * π t * (π h')⁻¹ * (π t)⁻¹ := by rw [hc']
      _ = 1 := by group
  · rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hn]
    calc (π t)⁻¹ * (π h' * π t * (π h')⁻¹ * (π t)⁻¹) * π t * (π h' * π t * (π h')⁻¹ * (π t)⁻¹)
        = (π t)⁻¹ * (π h' * (π t * π t) * (π h')⁻¹) * (π t)⁻¹ := by group
      _ = (π t)⁻¹ * (π t * π t) * (π t)⁻¹ := by rw [hc'']
      _ = 1 := by group

theorem Hyp.a_mul_a (h : Hyp H K₁ K₂ z T a) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h.a_ord, sq] at this

theorem Hyp.a_inv (h : Hyp H K₁ K₂ z T a) : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.a_mul_a

theorem Hyp.not_trivial_both (h : Hyp H K₁ K₂ z T a) (h1 : ∀ x ∈ K₁, a * x * a⁻¹ = x)
    (h2 : ∀ x ∈ K₂, a * x * a⁻¹ = x) : False := by
  have hS := h.setting
  have hcent : a ∈ centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := (mem_sup_of_comm hS.comm m).mp hm
    have f1 : a * m₁ = m₁ * a := mul_inv_eq_iff_eq_mul.mp (h1 m₁ hm₁)
    have f2 : a * m₂ = m₂ * a := mul_inv_eq_iff_eq_mul.mp (h2 m₂ hm₂)
    calc m₁ * m₂ * a = m₁ * (m₂ * a) := by group
      _ = m₁ * (a * m₂) := by rw [f2]
      _ = (m₁ * a) * m₂ := by group
      _ = (a * m₁) * m₂ := by rw [f1]
      _ = a * (m₁ * m₂) := by group
  exact h.a_not_mem_K (hS.centralizer_le hcent)

omit [Finite H] in
theorem inner_of_twist_gen {L M : Subgroup H} (hLM : ∀ a ∈ L, ∀ b ∈ M, a * b = b * a)
    {a t kL kM y : H} (ha : a⁻¹ = a) (hkL : kL ∈ L)
    (hk : t * a * t⁻¹ = (kL * kM) * a⁻¹) (hy : y ∈ M)
    (htriv : a * (t⁻¹ * y * t) * a⁻¹ = t⁻¹ * y * t) :
    a * y * a⁻¹ = kM⁻¹ * y * kM⁻¹⁻¹ := by
  have e1 : (t * a * t⁻¹) * y * (t * a * t⁻¹)⁻¹ = y := by
    calc (t * a * t⁻¹) * y * (t * a * t⁻¹)⁻¹ = t * (a * (t⁻¹ * y * t) * a⁻¹) * t⁻¹ := by group
      _ = t * (t⁻¹ * y * t) * t⁻¹ := by rw [htriv]
      _ = y := by group
  rw [hk] at e1
  have e3 : a⁻¹ * y * a = (kL * kM)⁻¹ * y * (kL * kM) := by
    calc a⁻¹ * y * a = (kL * kM)⁻¹ * (((kL * kM) * a⁻¹) * y * ((kL * kM) * a⁻¹)⁻¹) * (kL * kM) := by
          group
      _ = (kL * kM)⁻¹ * y * (kL * kM) := by rw [e1]
  have e4 : (kL * kM)⁻¹ * y * (kL * kM) = kM⁻¹ * y * kM := by
    have hc := hLM kL hkL y hy
    have h5 : kL⁻¹ * y * kL = y := by
      calc kL⁻¹ * y * kL = kL⁻¹ * (y * kL) := by group
        _ = kL⁻¹ * (kL * y) := by rw [hc]
        _ = y := by group
    calc (kL * kM)⁻¹ * y * (kL * kM) = kM⁻¹ * (kL⁻¹ * y * kL) * kM := by group
      _ = kM⁻¹ * y * kM := by rw [h5]
  calc a * y * a⁻¹ = a⁻¹ * y * a := by rw [ha]
    _ = kM⁻¹ * y * kM := e3.trans e4
    _ = kM⁻¹ * y * kM⁻¹⁻¹ := by group

theorem Hyp.nontrivial_both (h : Hyp H K₁ K₂ z T a) (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) :
    (¬ ∀ x ∈ K₁, a * x * a⁻¹ = x) ∧ (¬ ∀ x ∈ K₂, a * x * a⁻¹ = x) := by
  have hS := h.setting
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ normalizer (K₁ : Set H) := by
    have := h.T1_lt h2A7
    obtain ⟨t, htT, htn⟩ := Set.exists_of_ssubset this
    exact ⟨t, htT, fun hh => htn ⟨htT, hh⟩⟩
  obtain ⟨h', -, -, hV, hV'⟩ := h.exists_comm_rep h2A7 htT htN
  have htN' : t⁻¹ ∉ normalizer (K₁ : Set H) := fun hh => htN (by simpa using Subgroup.inv_mem _ hh)
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  ·
    refine h.not_trivial_both h1 (h.f₂.inner_trivial hS.type₂ ?_)
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := (mem_sup_of_comm hS.comm _).mp hV
    refine ⟨k₂⁻¹, K₂.inv_mem hk₂, fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t ∈ K₁ := by
      have := hS.conj_mem_swap₂ htN' hy
      simpa using this
    have e2 : t * a * t⁻¹ = (k₁ * k₂) * a⁻¹ := by
      rw [← hk]; group
    exact inner_of_twist_gen hS.comm h.a_inv hk₁ e2 hy (h1 _ hy')
  ·
    refine h.not_trivial_both (h.f₁.inner_trivial hS.type₁ ?_) h2
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := (mem_sup_of_comm hS.comm _).mp hV'
    refine ⟨k₁⁻¹, K₁.inv_mem hk₁, fun y hy => ?_⟩
    have hy' : t * y * t⁻¹ ∈ K₂ := hS.conj_mem_swap₁ htN hy
    have e2 : t⁻¹ * a * t⁻¹⁻¹ = (k₂ * k₁) * a⁻¹ := by
      have hc := hS.comm k₁ hk₁ k₂ hk₂
      have : k₂ * k₁ = k₁ * k₂ := hc.symm
      rw [this, ← hk]; group
    have := inner_of_twist_gen (L := K₂) (M := K₁) (fun a ha b hb => (hS.comm b hb a ha).symm) h.a_inv hk₂
      e2 hy (by simpa using h2 _ hy')
    exact this

theorem prod3_Ca (h2A7 : CFSG.GH74.GLS.IVK.Lifted.II4_2A7) (h : Hyp H K₁ K₂ z T a) :
    Ca T K₁ K₂ a := by
  refine ⟨h.T1_lt h2A7, (h.nontrivial_both h2A7).1, (h.nontrivial_both h2A7).2, ?_⟩
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ normalizer (K₁ : Set H) := by
    have := h.T1_lt h2A7
    obtain ⟨t, htT, htn⟩ := Set.exists_of_ssubset this
    exact ⟨t, htT, fun hh => htn ⟨htT, hh⟩⟩
  obtain ⟨h', hh', hP, -, -⟩ := h.exists_comm_rep h2A7 htT htN
  refine ⟨h', hh'.1, t, htT, fun hc => ?_⟩
  rw [commutatorElement_def] at hc
  have h1 : a⁻¹ ∈ P T K₁ K₂ := by
    have := (P T K₁ K₂).mul_mem hP ((P T K₁ K₂).inv_mem hc)
    simpa [mul_assoc] using this
  have h2 : a ∈ P T K₁ K₂ := by simpa using (P T K₁ K₂).inv_mem h1
  exact h.a_not_mem_K h2.2

end CaH

end CFSG.GH74.GLS.IVK.Prod3
