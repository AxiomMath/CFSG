module

public import CFSG.GH74.GLS.IVK.Lifted.Alt51d

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Equiv CFSG CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {K : Subgroup H} {n : ℕ}

structure PermRep.KerData (R : PermRep K n) (z : H) : Prop where
  ne_one : z ≠ 1
  sq : z * z = 1
  central : ∀ g : H, g * z = z * g
  ρ_z : R.ρ z = 1
  ker : ∀ x : H, R.ρ x = 1 → x = 1 ∨ x = z

theorem PermRep.exists_kerData (R : PermRep K n) : ∃ z : H, R.KerData z := by
  classical
  obtain ⟨z, hzc, hz1, hz2, hzk⟩ := R.cover.exists_z
  have hzker : z ∈ R.π.ker := by
    have hne : R.π.ker ≠ ⊥ := by
      intro h
      have := R.cover.card_ker
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    rcases hzk (a : ↥K) a.2 with h1 | h1
    · exact absurd (Subtype.ext h1) ha
    · rw [← h1]
      exact a.2
  have hρz : R.ρ (z : H) = 1 := by
    rw [R.ρ_K]
    have : R.π z = 1 := hzker
    rw [this]
    rfl
  have hker2 : ∀ x : H, R.ρ x = 1 → x = 1 ∨ x = (z : H) := by
    intro x hx
    obtain ⟨k, rfl, hk⟩ := R.ker_ρ x hx
    rcases hzk k hk with h1 | h1
    · left
      rw [h1]
      rfl
    · right
      rw [h1]
  have hzH1 : (z : H) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzcen : ∀ g : H, g * (z : H) = (z : H) * g := by
    intro g
    have h1 : R.ρ (g * (z : H) * g⁻¹) = 1 := by
      rw [map_mul, map_mul, hρz, mul_one, map_inv, mul_inv_cancel]
    rcases hker2 _ h1 with h | h
    · exfalso
      apply hzH1
      have : (z : H) = g⁻¹ * (g * (z : H) * g⁻¹) * g := by group
      rw [this, h]
      group
    · calc g * (z : H) = (g * (z : H) * g⁻¹) * g := by group
        _ = (z : H) * g := by rw [h]
  have hzsq : (z : H) * (z : H) = 1 := by
    have := congrArg Subtype.val (show z * z = 1 by rw [← pow_two]; exact hz2)
    simpa using this
  exact ⟨(z : H), ⟨hzH1, hzsq, hzcen, hρz, hker2⟩⟩

section PermAux

variable {α : Type*} [DecidableEq α]

theorem swap_klein {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab : a ≠ b) : swap a b * swap c d * (swap a c * swap b d) = swap a d * swap b c := by
  ext x
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem swap_comm_swap {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  ext x
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem peel [Fintype α] (σ : Perm α) (hσ : σ * σ = 1) {e : α} (he : σ e ≠ e) :
    (swap e (σ e) * σ) * (swap e (σ e) * σ) = 1 ∧ (swap e (σ e) * σ) e = e ∧
      (swap e (σ e) * σ) (σ e) = σ e ∧ (∀ x, σ x = x → (swap e (σ e) * σ) x = x) ∧
      (swap e (σ e) * σ).support.card < σ.support.card := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Perm α => p x) hσ
    simpa using this
  have hcomm : σ * swap e (σ e) = swap e (σ e) * σ := by
    have h := swap_apply_apply σ e (σ e)
    rw [hσσ, swap_comm] at h
    calc σ * swap e (σ e) = (σ * swap e (σ e) * σ⁻¹) * σ := by group
      _ = swap e (σ e) * σ := by rw [← h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc (swap e (σ e) * σ) * (swap e (σ e) * σ) = swap e (σ e) * (σ * swap e (σ e)) * σ := by group
      _ = swap e (σ e) * (swap e (σ e) * σ) * σ := by rw [hcomm]
      _ = (swap e (σ e) * swap e (σ e)) * (σ * σ) := by group
      _ = 1 := by rw [swap_mul_self, hσ, mul_one]
  · simp [Perm.mul_apply]
  · simp [Perm.mul_apply, hσσ]
  · intro x hx
    simp only [Perm.mul_apply, hx]
    apply swap_apply_of_ne_of_ne
    · intro h
      apply he
      rw [← h, hx]
    · intro h
      exact he (by
        calc σ e = x := h.symm
          _ = σ x := hx.symm
          _ = σ (σ e) := by rw [h]
          _ = e := hσσ e)
  · exact Equiv.Perm.card_support_swap_mul he


omit [DecidableEq α] in
theorem fixed_ne (τ : Perm α) (hτ : τ * τ = 1) {e : α} (he : τ e ≠ e) {x : α} (hx : τ x = x) :
    x ≠ e ∧ x ≠ τ e := by
  have hσσ : ∀ y, τ (τ y) = y := fun y => by
    have := congrArg (fun p : Perm α => p y) hτ
    simpa using this
  refine ⟨fun h => he (h ▸ hx), fun h => ?_⟩
  apply he
  calc τ e = x := h.symm
    _ = τ x := hx.symm
    _ = τ (τ e) := by rw [h]
    _ = e := hσσ e

theorem disjoint_swap_pairs {e f e' f' a c b d : α} (h : [e, f, e', f', a, c, b, d].Nodup) :
    Equiv.Perm.Disjoint (swap e f * swap e' f') (swap a c * swap b d) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨hee, hef, hea, hec, heb, hed⟩, ⟨hfe', hfa, hfc, hfb, hfd⟩, ⟨he'a, he'c, he'b, he'd⟩,
    ⟨hf'a, hf'c, hf'b, hf'd⟩, ⟨hac, hab, had⟩, ⟨hcb, hcd⟩, hbd⟩ := h
  refine Equiv.Perm.Disjoint.mul_left (Equiv.Perm.Disjoint.mul_right ?_ ?_) (Equiv.Perm.Disjoint.mul_right ?_ ?_)
  · exact Equiv.Perm.disjoint_swap_swap (by simp [*])
  · exact Equiv.Perm.disjoint_swap_swap (by simp [*])
  · exact Equiv.Perm.disjoint_swap_swap (by simp [*])
  · exact Equiv.Perm.disjoint_swap_swap (by simp [*])

end PermAux

namespace PermRep

variable {R : PermRep K n} {z : H}

theorem KerData.sq_central (hz : R.KerData z) {x : H} (hx : R.ρ x = 1) :
    (∀ g : H, g * x = x * g) ∧ x * x = 1 := by
  rcases hz.ker x hx with h | h
  · subst h
    exact ⟨fun g => by simp, by simp⟩
  · subst h
    exact ⟨hz.central, hz.sq⟩

theorem KerData.cm_eq_sq (hz : R.KerData z) {u v : H} (hu : R.ρ u * R.ρ u = 1) (huv : u * u = v * v) :
    u⁻¹ * v * u * v⁻¹ = (u * v) * (u * v) := by
  have hρu2 : R.ρ (u * u) = 1 := by rw [map_mul]; exact hu
  obtain ⟨hεc, hε2⟩ := hz.sq_central hρu2
  obtain ⟨k, hkdef⟩ : ∃ k, k = u⁻¹ * v * u * v⁻¹ := ⟨_, rfl⟩
  have hk : (u * v) * (u * v) = (u * u) * k * (v * v) := by rw [hkdef]; group
  have hε : (u * u) * k * (u * u) = k := by
    calc (u * u) * k * (u * u) = (u * u) * (k * (u * u)) := by group
      _ = (u * u) * ((u * u) * k) := by rw [hεc k]
      _ = ((u * u) * (u * u)) * k := by group
      _ = k := by rw [hε2, one_mul]
  rw [hk, ← huv, hε, hkdef]


theorem sign_eq_one_of_cycleType_two_two {σ : Perm (Fin n)} (hσ : σ.cycleType = {2, 2}) :
    Perm.sign σ = 1 := by
  rw [Perm.sign_of_cycleType, hσ]
  decide

theorem sign_eq_one_of_cycleType_two_two_two_two {σ : Perm (Fin n)} (hσ : σ.cycleType = {2, 2, 2, 2}) :
    Perm.sign σ = 1 := by
  rw [Perm.sign_of_cycleType, hσ]
  decide

theorem KerData.sq_double (hz : R.KerData z) (hn : 5 ≤ n) {x : H} (hx : (R.ρ x).cycleType = {2, 2}) :
    x * x = z := by
  have hxK : x ∈ K := R.mem_K_of_sign x (sign_eq_one_of_cycleType_two_two hx)
  have hcyc : ((R.π ⟨x, hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2} := by
    rw [← R.ρ_K ⟨x, hxK⟩]
    exact hx
  obtain ⟨hk, h1⟩ := R.cover.sq_mem_ker_ne_one_of_cycleType_two_two hn hcyc
  have hcoe : ((⟨x, hxK⟩ ^ 2 : ↥K) : H) = x * x := by simp [pow_two]
  have hρ : R.ρ (x * x) = 1 := by
    have h2 := R.ρ_K (⟨x, hxK⟩ ^ 2)
    rw [hcoe] at h2
    rw [h2]
    have h3 : R.π (⟨x, hxK⟩ ^ 2) = 1 := hk
    rw [h3]
    rfl
  rcases hz.ker (x * x) hρ with h | h
  · exfalso
    apply h1
    apply Subtype.ext
    rw [hcoe, h]
    rfl
  · exact h

theorem sq_four (hn : 8 ≤ n) {x : H} (hx : (R.ρ x).cycleType = {2, 2, 2, 2}) : x * x = 1 := by
  have hxK : x ∈ K := R.mem_K_of_sign x (sign_eq_one_of_cycleType_two_two_two_two hx)
  have hcyc : ((R.π ⟨x, hxK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} := by
    rw [← R.ρ_K ⟨x, hxK⟩]
    exact hx
  have h1 := R.cover.sq_eq_one_of_cycleType_two_two_two_two hn hcyc
  have hcoe : ((⟨x, hxK⟩ ^ 2 : ↥K) : H) = x * x := by simp [pow_two]
  have := congrArg Subtype.val h1
  rw [hcoe] at this
  simpa using this

theorem KerData.anti_dd (hz : R.KerData z) (hn : 5 ≤ n) {u v : H} (hu : (R.ρ u).cycleType = {2, 2})
    (hv : (R.ρ v).cycleType = {2, 2}) (huv : (R.ρ (u * v)).cycleType = {2, 2}) :
    u⁻¹ * v * u = z * v := by
  have hu2 := hz.sq_double hn hu
  have hv2 := hz.sq_double hn hv
  have hρu : R.ρ u * R.ρ u = 1 := by rw [← map_mul, hu2, hz.ρ_z]
  have h := hz.cm_eq_sq (v := v) hρu (by rw [hu2, hv2])
  rw [hz.sq_double hn huv] at h
  calc u⁻¹ * v * u = (u⁻¹ * v * u * v⁻¹) * v := by group
    _ = z * v := by rw [h]

theorem KerData.comm_dd (hz : R.KerData z) (hn : 8 ≤ n) {u v : H} (hu : (R.ρ u).cycleType = {2, 2})
    (hv : (R.ρ v).cycleType = {2, 2}) (huv : (R.ρ (u * v)).cycleType = {2, 2, 2, 2}) :
    u⁻¹ * v * u = v := by
  have hu2 := hz.sq_double (by omega) hu
  have hv2 := hz.sq_double (by omega) hv
  have hρu : R.ρ u * R.ρ u = 1 := by rw [← map_mul, hu2, hz.ρ_z]
  have h := hz.cm_eq_sq (v := v) hρu (by rw [hu2, hv2])
  rw [sq_four hn huv] at h
  calc u⁻¹ * v * u = (u⁻¹ * v * u * v⁻¹) * v := by group
    _ = v := by rw [h, one_mul]

theorem KerData.sq_tt_eq (hz : R.KerData z) (hsurj : Function.Surjective R.ρ) {u v : H}
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (had : a ≠ d)
    (hu : R.ρ u = swap a b) (hv : R.ρ v = swap c d) : u * u = v * v := by
  obtain ⟨g, hg⟩ := hsurj (swap a c * swap b d)
  have hσa : (swap a c * swap b d) a = c := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left]
  have hσb : (swap a c * swap b d) b = d := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne had.symm hcd.symm]
  have hconj : R.ρ (g * u * g⁻¹) = R.ρ v := by
    rw [map_mul, map_mul, map_inv, hg, hu, hv, ← swap_apply_apply, hσa, hσb]
  have hker : R.ρ (v⁻¹ * (g * u * g⁻¹)) = 1 := by
    rw [map_mul, map_inv, hconj, inv_mul_cancel]
  have hρu2 : R.ρ (u * u) = 1 := by rw [map_mul, hu, swap_mul_self]
  obtain ⟨hεc, -⟩ := hz.sq_central hρu2
  have hsq : (g * u * g⁻¹) * (g * u * g⁻¹) = u * u := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = (u * u) * g * g⁻¹ := by rw [hεc g]
      _ = u * u := by group
  rcases hz.ker _ hker with h | h
  · have : g * u * g⁻¹ = v := by
      calc g * u * g⁻¹ = v * (v⁻¹ * (g * u * g⁻¹)) := by group
        _ = v := by rw [h, mul_one]
    rw [← hsq, this]
  · have : g * u * g⁻¹ = v * z := by
      calc g * u * g⁻¹ = v * (v⁻¹ * (g * u * g⁻¹)) := by group
        _ = v * z := by rw [h]
    have hvz : (v * z) * (v * z) = v * v := by
      calc (v * z) * (v * z) = v * (z * v) * z := by group
        _ = v * (v * z) * z := by rw [← hz.central v]
        _ = (v * v) * (z * z) := by group
        _ = v * v := by rw [hz.sq, mul_one]
    rw [← hsq, this, hvz]

theorem KerData.anti_tt (hz : R.KerData z) (hn : 5 ≤ n) (hsurj : Function.Surjective R.ρ) {u v : H}
    {a b c d : Fin n} (hnd : [a, b, c, d].Nodup) (hu : R.ρ u = swap a b) (hv : R.ρ v = swap c d) :
    u⁻¹ * v * u = z * v := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hnd
  have hρu : R.ρ u * R.ρ u = 1 := by rw [hu, swap_mul_self]
  have h := hz.cm_eq_sq (v := v) hρu (hz.sq_tt_eq hsurj hab hcd had hu hv)
  have hcyc : (R.ρ (u * v)).cycleType = {2, 2} := by
    rw [map_mul, hu, hv]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by simp [hab, hac, had, hbc, hbd, hcd])
  rw [hz.sq_double hn hcyc] at h
  calc u⁻¹ * v * u = (u⁻¹ * v * u * v⁻¹) * v := by group
    _ = z * v := by rw [h]


theorem lift_even (R : PermRep K n) {σ : Perm (Fin n)} (h : Perm.sign σ = 1) : ∃ x : H, R.ρ x = σ := by
  obtain ⟨k, hk⟩ := R.cover.surj ⟨σ, Perm.mem_alternatingGroup.2 h⟩
  exact ⟨k, by rw [R.ρ_K, hk]⟩

theorem surj_of_odd (R : PermRep K n) {h₀ : H} (hodd : Perm.sign (R.ρ h₀) = -1) :
    Function.Surjective R.ρ := by
  intro σ
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact R.lift_even h1
  · have h2 : Perm.sign (σ * (R.ρ h₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, hodd]
      decide
    obtain ⟨k, hk⟩ := R.lift_even h2
    refine ⟨k * h₀, ?_⟩
    rw [map_mul, hk]
    group

theorem KerData.conj_eq_of_ρ_eq (hz : R.KerData z) {g g' : H} (h : R.ρ g = R.ρ g') (x : H) :
    g⁻¹ * x * g = g'⁻¹ * x * g' := by
  have hker : R.ρ (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases hz.ker _ hker with h1 | h1
  · have : g = g' := by
      calc g = g' * (g'⁻¹ * g) := by group
        _ = g' := by rw [h1, mul_one]
    rw [this]
  · have : g = g' * z := by
      calc g = g' * (g'⁻¹ * g) := by group
        _ = g' * z := by rw [h1]
    rw [this]
    calc (g' * z)⁻¹ * x * (g' * z) = z⁻¹ * (g'⁻¹ * x * g' * z) := by group
      _ = z⁻¹ * (z * (g'⁻¹ * x * g')) := by rw [hz.central (g'⁻¹ * x * g')]
      _ = g'⁻¹ * x * g' := by group

theorem KerData.comm_tt_dd (hz : R.KerData z) (hn : 5 ≤ n) (hsurj : Function.Surjective R.ρ) {u g : H}
    {a b c d e f : Fin n} (hac : a ≠ c) (hbd : b ≠ d) (hef : e ≠ f) (he : e ∉ [a, b, c, d])
    (hf : f ∉ [a, b, c, d]) (hu : R.ρ u = swap e f) (hg : R.ρ g = swap a c * swap b d) :
    g⁻¹ * u * g = u := by
  obtain ⟨hea, heb, hec, hed⟩ : e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by simpa using he
  obtain ⟨hfa, hfb, hfc, hfd⟩ : f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d := by simpa using hf
  obtain ⟨s₁, hs₁⟩ := hsurj (swap a c)
  obtain ⟨s₂, hs₂⟩ := hsurj (swap b d)
  have h1 : s₁⁻¹ * u * s₁ = z * u :=
    hz.anti_tt hn hsurj (by simp [hac, hef, hea.symm, hfa.symm, hec.symm, hfc.symm]) hs₁ hu
  have h2 : s₂⁻¹ * u * s₂ = z * u :=
    hz.anti_tt hn hsurj (by simp [hbd, hef, heb.symm, hfb.symm, hed.symm, hfd.symm]) hs₂ hu
  rw [hz.conj_eq_of_ρ_eq (g' := s₁ * s₂) (by rw [map_mul, hs₁, hs₂, hg]) u]
  calc (s₁ * s₂)⁻¹ * u * (s₁ * s₂) = s₂⁻¹ * (s₁⁻¹ * u * s₁) * s₂ := by group
    _ = s₂⁻¹ * (z * u) * s₂ := by rw [h1]
    _ = (s₂⁻¹ * z) * u * s₂ := by group
    _ = (z * s₂⁻¹) * u * s₂ := by rw [hz.central s₂⁻¹]
    _ = z * (s₂⁻¹ * u * s₂) := by group
    _ = z * (z * u) := by rw [h2]
    _ = u := by rw [← mul_assoc, hz.sq, one_mul]


theorem KerData.comm_rest (hz : R.KerData z) (hn : 8 ≤ n) {a b c d : Fin n} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : a ≠ b) (hbc : b ≠ c) (had : a ≠ d) (hcd : c ≠ d) {g : H}
    (hg : R.ρ g = swap a c * swap b d) :
    ∀ (m : ℕ) (r : H), (R.ρ r).support.card ≤ m → R.ρ r * R.ρ r = 1 → R.ρ r a = a → R.ρ r b = b →
      R.ρ r c = c → R.ρ r d = d → g⁻¹ * r * g = r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro r hm hsq ha hb hc hd
  by_cases hr1 : R.ρ r = 1
  · rcases hz.ker r hr1 with h | h
    · rw [h]
      group
    · rw [h]
      calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
        _ = g⁻¹ * (g * z) := by rw [hz.central g]
        _ = z := by group
  · obtain ⟨e, he⟩ : ∃ e, R.ρ r e ≠ e := by
      by_contra hcon
      push Not at hcon
      exact hr1 (Equiv.ext hcon)
    obtain ⟨hp1, hpe, hpf, hpx, hpc⟩ := peel (R.ρ r) hsq he
    have hfx : ∀ x : Fin n, R.ρ r x = x → x ≠ e ∧ x ≠ R.ρ r e := fun x hx => fixed_ne (R.ρ r) hsq he hx
    generalize hf : R.ρ r e = f at hp1 hpe hpf hpx hpc he hfx
    obtain ⟨hae, haf⟩ := hfx a ha
    obtain ⟨hbe, hbf⟩ := hfx b hb
    obtain ⟨hce, hcf⟩ := hfx c hc
    obtain ⟨hde, hdf⟩ := hfx d hd
    have hef : e ≠ f := fun h => he (by rw [← h])
    by_cases hr' : swap e f * R.ρ r = 1
    · have hρr : R.ρ r = swap e f := by
        have : R.ρ r = (swap e f)⁻¹ := eq_inv_of_mul_eq_one_right hr'
        rw [this, swap_inv]
      have hsurj : Function.Surjective R.ρ :=
        R.surj_of_odd (h₀ := r) (by rw [hρr, Perm.sign_swap hef])
      exact hz.comm_tt_dd (by omega) hsurj hac hbd hef (by simp [hae.symm, hbe.symm, hce.symm, hde.symm])
        (by simp [haf.symm, hbf.symm, hcf.symm, hdf.symm]) hρr hg
    · obtain ⟨e', he'⟩ : ∃ e', (swap e f * R.ρ r) e' ≠ e' := by
        by_contra hcon
        push Not at hcon
        exact hr' (Equiv.ext hcon)
      obtain ⟨hq1, hqe, hqf, hqx, hqc⟩ := peel (swap e f * R.ρ r) hp1 he'
      have hfx' : ∀ x : Fin n, (swap e f * R.ρ r) x = x → x ≠ e' ∧ x ≠ (swap e f * R.ρ r) e' :=
        fun x hx => fixed_ne (swap e f * R.ρ r) hp1 he' hx
      generalize hf' : (swap e f * R.ρ r) e' = f' at hq1 hqe hqf hqx hqc he' hfx'
      obtain ⟨hae', haf'⟩ := hfx' a (hpx a ha)
      obtain ⟨hbe', hbf'⟩ := hfx' b (hpx b hb)
      obtain ⟨hce', hcf'⟩ := hfx' c (hpx c hc)
      obtain ⟨hde', hdf'⟩ := hfx' d (hpx d hd)
      have hee : e ≠ e' := (hfx' e hpe).1
      have hfe' : f ≠ e' := (hfx' f hpf).1
      have hef' : e ≠ f' := (hfx' e hpe).2
      have hff' : f ≠ f' := (hfx' f hpf).2
      have hef'' : e' ≠ f' := he'.symm
      have hδ : Perm.sign (swap e f * swap e' f') = 1 := by
        rw [map_mul, Perm.sign_swap hef, Perm.sign_swap hef'']
        decide
      obtain ⟨d₀, hd₀⟩ := R.lift_even hδ
      obtain ⟨r'', hr''⟩ : ∃ r'', r'' = d₀⁻¹ * r := ⟨_, rfl⟩
      have hρr'' : R.ρ r'' = swap e' f' * (swap e f * R.ρ r) := by
        rw [hr'', map_mul, map_inv, hd₀, mul_inv_rev, swap_inv, swap_inv, mul_assoc]
      have hlt : (swap e' f' * (swap e f * R.ρ r)).support.card < m := by
        omega
      have hIH : g⁻¹ * r'' * g = r'' := by
        refine ih _ hlt r'' (by rw [hρr'']) (by rw [hρr'']; exact hq1) ?_ ?_ ?_ ?_
        · rw [hρr'']
          exact hqx a (hpx a ha)
        · rw [hρr'']
          exact hqx b (hpx b hb)
        · rw [hρr'']
          exact hqx c (hpx c hc)
        · rw [hρr'']
          exact hqx d (hpx d hd)
      have hnd1 : [e, f, e', f'].Nodup := by simp [hef, hee, hef', hfe', hff', hef'']
      have hnd2 : [a, c, b, d].Nodup := by
        simp [hac, hab, had, hbc.symm, hcd, hbd]
      have hcyc1 : (R.ρ d₀).cycleType = {2, 2} := by
        rw [hd₀]
        exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd1
      have hcyc2 : (R.ρ g).cycleType = {2, 2} := by
        rw [hg]
        exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd2
      have hcyc3 : (R.ρ (d₀ * g)).cycleType = {2, 2, 2, 2} := by
        have hdis := disjoint_swap_pairs (e := e) (f := f) (e' := e') (f' := f') (a := a) (c := c) (b := b)
          (d := d) (by
            simp [hef, hee, hef', hfe', hff', hef'', hae.symm, haf.symm, hae'.symm, haf'.symm, hac, hab,
              had, hbc.symm, hbd, hcd, hbe.symm, hbf.symm, hbe'.symm, hbf'.symm, hce.symm, hcf.symm, hce'.symm,
              hcf'.symm, hde.symm, hdf.symm, hde'.symm, hdf'.symm])
        rw [map_mul, hd₀, hg, hdis.cycleType_mul, Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd1,
          Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd2]
        rfl
      have hdg : d₀⁻¹ * g * d₀ = g := hz.comm_dd hn hcyc1 hcyc2 hcyc3
      have hgd : g * d₀ = d₀ * g := by
        calc g * d₀ = d₀ * (d₀⁻¹ * g * d₀) := by group
          _ = d₀ * g := by rw [hdg]
      have hcomm_dg : g⁻¹ * d₀ * g = d₀ := by
        calc g⁻¹ * d₀ * g = g⁻¹ * (d₀ * g) := by group
          _ = g⁻¹ * (g * d₀) := by rw [hgd]
          _ = d₀ := by group
      have hr : r = d₀ * r'' := by rw [hr'']; group
      calc g⁻¹ * r * g = (g⁻¹ * d₀ * g) * (g⁻¹ * r'' * g) := by
            conv_lhs => rw [hr]
            group
        _ = d₀ * r'' := by rw [hcomm_dg, hIH]
        _ = r := hr.symm


theorem KerData.exists_conj_mul_z (hz : R.KerData z) (hn : 8 ≤ n) {w : H} (hw2 : R.ρ w * R.ρ w = 1)
    (hw1 : R.ρ w ≠ 1) : ∃ g : H, g⁻¹ * w * g = z * w := by
  classical
  have hww : ∀ x, R.ρ w (R.ρ w x) = x := fun x => by
    have := congrArg (fun p : Perm (Fin n) => p x) hw2
    simpa using this
  by_cases hswap : ∃ a b : Fin n, a ≠ b ∧ R.ρ w = swap a b
  · obtain ⟨a, b, hab, hw⟩ := hswap
    have hsurj : Function.Surjective R.ρ := R.surj_of_odd (h₀ := w) (by rw [hw, Perm.sign_swap hab])
    have hcard : 1 < ((Finset.univ : Finset (Fin n)) \ {a, b}).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]
      have : ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨c, hc, e, he, hce⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hc he
    obtain ⟨g, hg⟩ := hsurj (swap c e)
    have hnd : [c, e, a, b].Nodup := by
      simp [hce, hc.1, hc.2, he.1, he.2, hab]
    exact ⟨g, hz.anti_tt (by omega) hsurj hnd hg hw⟩
  · push Not at hswap
    obtain ⟨a, ha⟩ : ∃ a, R.ρ w a ≠ a := by
      by_contra hcon
      push Not at hcon
      exact hw1 (Equiv.ext hcon)
    obtain ⟨b, hb⟩ : ∃ b, R.ρ w a = b := ⟨_, rfl⟩
    rw [hb] at ha
    have hwb : R.ρ w b = a := by rw [← hb, hww]
    obtain ⟨c, hc1, hc2, hc3⟩ : ∃ c, R.ρ w c ≠ c ∧ c ≠ a ∧ c ≠ b := by
      by_contra hcon
      push Not at hcon
      apply hswap a b (Ne.symm ha)
      ext x
      by_cases hx : R.ρ w x = x
      · have hxa : x ≠ a := fun h => ha (by rw [← hb, ← h, hx])
        have hxb : x ≠ b := fun h => by
          have h1 : R.ρ w b = b := h ▸ hx
          exact ha (h1.symm.trans hwb)
        rw [hx, swap_apply_of_ne_of_ne hxa hxb]
      · rcases eq_or_ne x a with h | h
        · rw [h, hb, swap_apply_left]
        · have hxb : x = b := hcon x hx h
          rw [hxb, swap_apply_right, hwb]
    obtain ⟨d, hd⟩ : ∃ d, R.ρ w c = d := ⟨_, rfl⟩
    rw [hd] at hc1
    have hwd : R.ρ w d = c := by rw [← hd, hww]
    have hda : d ≠ a := fun h => hc3 (by rw [← hwd, h, hb])
    have hdb : d ≠ b := fun h => hc2 (by rw [← hwd, h, hwb])
    have hab : a ≠ b := ha.symm
    have hac : a ≠ c := hc2.symm
    have hbc : b ≠ c := hc3.symm
    have hcd : c ≠ d := hc1.symm
    have had : a ≠ d := hda.symm
    have hbd : b ≠ d := hdb.symm
    have hnd1 : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    have hnd2 : [a, c, b, d].Nodup := by simp [hac, hab, had, hbc.symm, hcd, hbd]
    have hnd3 : [a, d, b, c].Nodup := by simp [had, hab, hac, hbd.symm, hcd.symm, hbc]
    have hsv : Perm.sign (swap a b * swap c d) = 1 := by
      rw [map_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
      decide
    have hsg : Perm.sign (swap a c * swap b d) = 1 := by
      rw [map_mul, Perm.sign_swap hac, Perm.sign_swap hbd]
      decide
    obtain ⟨v, hv⟩ := R.lift_even hsv
    obtain ⟨g, hg⟩ := R.lift_even hsg
    obtain ⟨r, hr⟩ : ∃ r, r = v⁻¹ * w := ⟨_, rfl⟩
    have hρr : R.ρ r = (swap c d * swap a b) * R.ρ w := by
      rw [hr, map_mul, map_inv, hv, mul_inv_rev, swap_inv, swap_inv]
    have hra : R.ρ r a = a := by
      rw [hρr, Perm.mul_apply, Perm.mul_apply, hb, swap_apply_right, swap_apply_of_ne_of_ne hac had]
    have hrb : R.ρ r b = b := by
      rw [hρr, Perm.mul_apply, Perm.mul_apply, hwb, swap_apply_left,
        swap_apply_of_ne_of_ne hbc.symm.symm hbd]
    have hrc : R.ρ r c = c := by
      rw [hρr, Perm.mul_apply, Perm.mul_apply, hd, swap_apply_of_ne_of_ne hda hdb, swap_apply_right]
    have hrd : R.ρ r d = d := by
      rw [hρr, Perm.mul_apply, Perm.mul_apply, hwd, swap_apply_of_ne_of_ne hac.symm hbc.symm,
        swap_apply_left]
    have hcomm : swap a b * swap c d = swap c d * swap a b := swap_comm_swap hac had hbc hbd
    have hVV : (swap c d * swap a b) * (swap c d * swap a b) = 1 := by
      calc (swap c d * swap a b) * (swap c d * swap a b)
          = swap c d * (swap a b * swap c d) * swap a b := by group
        _ = swap c d * (swap c d * swap a b) * swap a b := by rw [hcomm]
        _ = (swap c d * swap c d) * (swap a b * swap a b) := by group
        _ = 1 := by rw [swap_mul_self, swap_mul_self, mul_one]
    have hWV : R.ρ w * (swap c d * swap a b) = (swap c d * swap a b) * R.ρ w := by
      have h1 := swap_apply_apply (R.ρ w) a b
      have h2 := swap_apply_apply (R.ρ w) c d
      rw [hb, hwb, swap_comm] at h1
      rw [hd, hwd, swap_comm] at h2
      have h3 : R.ρ w * (swap c d * swap a b) * (R.ρ w)⁻¹ = swap c d * swap a b := by
        calc R.ρ w * (swap c d * swap a b) * (R.ρ w)⁻¹
            = (R.ρ w * swap c d * (R.ρ w)⁻¹) * (R.ρ w * swap a b * (R.ρ w)⁻¹) := by group
          _ = swap c d * swap a b := by rw [← h1, ← h2]
      calc R.ρ w * (swap c d * swap a b) = (R.ρ w * (swap c d * swap a b) * (R.ρ w)⁻¹) * R.ρ w := by group
        _ = (swap c d * swap a b) * R.ρ w := by rw [h3]
    have hrsq : R.ρ r * R.ρ r = 1 := by
      rw [hρr]
      calc (swap c d * swap a b) * R.ρ w * ((swap c d * swap a b) * R.ρ w)
          = (swap c d * swap a b) * (R.ρ w * (swap c d * swap a b)) * R.ρ w := by group
        _ = (swap c d * swap a b) * ((swap c d * swap a b) * R.ρ w) * R.ρ w := by rw [hWV]
        _ = ((swap c d * swap a b) * (swap c d * swap a b)) * (R.ρ w * R.ρ w) := by group
        _ = 1 := by rw [hVV, hw2, mul_one]
    have hgr : g⁻¹ * r * g = r :=
      hz.comm_rest hn hac hbd hab hbc had hcd hg _ r le_rfl hrsq hra hrb hrc hrd
    have hcycv : (R.ρ v).cycleType = {2, 2} := by
      rw [hv]
      exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd1
    have hcycg : (R.ρ g).cycleType = {2, 2} := by
      rw [hg]
      exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd2
    have hcycvg : (R.ρ (v * g)).cycleType = {2, 2} := by
      rw [map_mul, hv, hg, swap_klein hac had hbc hbd hcd hab]
      exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnd3
    have h1 : v⁻¹ * g * v = z * g := hz.anti_dd (by omega) hcycv hcycg hcycvg
    have h2 : g * v = z * (v * g) := by
      calc g * v = v * (v⁻¹ * g * v) := by group
        _ = v * (z * g) := by rw [h1]
        _ = (v * z) * g := by group
        _ = (z * v) * g := by rw [hz.central v]
        _ = z * (v * g) := by group
    have h3 : v * g = z * (g * v) := by
      calc v * g = (z * z) * (v * g) := by rw [hz.sq, one_mul]
        _ = z * (z * (v * g)) := by group
        _ = z * (g * v) := by rw [h2]
    have h4 : g⁻¹ * v * g = z * v := by
      calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
        _ = g⁻¹ * (z * (g * v)) := by rw [h3]
        _ = (g⁻¹ * z) * (g * v) := by group
        _ = (z * g⁻¹) * (g * v) := by rw [hz.central g⁻¹]
        _ = z * v := by group
    refine ⟨g, ?_⟩
    have hwv : w = v * r := by rw [hr]; group
    calc g⁻¹ * w * g = (g⁻¹ * v * g) * (g⁻¹ * r * g) := by
          conv_lhs => rw [hwv]
          group
      _ = (z * v) * r := by rw [h4, hgr]
      _ = z * w := by rw [hwv]; group

end PermRep

end CFSG.GH74.GLS.IVK.Lifted
