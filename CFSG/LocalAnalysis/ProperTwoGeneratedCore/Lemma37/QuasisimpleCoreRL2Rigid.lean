module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Central

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem conj_mul_self_of_anticomm (hc : PartC T Q P₁ e u) {v j : G} (hjQ : j ∈ Q)
    (hjv : j * v * j⁻¹ = v * e) : j * (v * u) * j⁻¹ = v * u * e := by
  have hju : j * u = u * j := hc.commute j hjQ u hc.self_mem
  calc j * (v * u) * j⁻¹ = (j * v * j⁻¹) * (j * u * j⁻¹) := by group
    _ = v * e * u := by rw [hjv, hju, mul_inv_cancel_right]
    _ = v * u * e := by rw [mul_assoc v e u, ← hc.commute_centralElt u]; group

theorem commute_mul_of_not_mem (hc : PartC T Q P₁ e u)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {v : G} (hvQ : v ∈ Q)
    (hvv : v * v = e) (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {t : G}
    (ht : t ∈ T) (htQ : t ∉ Q ⊔ P₁) (htt : t * t = e) : t * (v * u) = v * u * t := by
  have htv := hc.conj_eq_mul_centralElt ht htQ htt (Subgroup.mem_sup_left hvQ) hvv
    ((Subgroup.mem_normalizer_iff.mp (hTv ht) v).mp (Subgroup.mem_zpowers v))
  have htu := hc.conj_eq_mul_centralElt ht htQ htt (Subgroup.mem_sup_right hc.self_mem) hc.sq
    ((Subgroup.mem_normalizer_iff.mp (hnorm ht) u).mp (Subgroup.mem_zpowers u))
  have h : t * (v * u) * t⁻¹ = v * u := by
    calc t * (v * u) * t⁻¹ = (t * v * t⁻¹) * (t * u * t⁻¹) := by group
      _ = v * e * (u * e) := by rw [htv, htu]
      _ = v * u * (e * e) := by
        rw [mul_assoc v e, ← mul_assoc e u e, ← hc.commute_centralElt u]; group
      _ = v * u := by rw [hc.centralElt_mul_self, mul_one]
  calc t * (v * u) = t * (v * u) * t⁻¹ * t := by group
    _ = v * u * t := by rw [h]

theorem exists_conj_eq_of_conj_eq [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁)
    (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {j : G} (hjQ : j ∈ Q)
    (hjv : j * v * j⁻¹ = v * e) {x : G} (hxT : x ∈ T) (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e)
    {g : G} (hgx : g * x * g⁻¹ = u) :
    ∃ g' : G, g' * (v * u) = v * u * g' ∧ (g' * x * g'⁻¹ = u ∨ g' * x * g'⁻¹ = u * e) := by
  have he := hc.commute_centralElt
  have hxu : x * u * x⁻¹ = u * e := hc.conj_eq_mul_centralElt hxT hx hxx
    (Subgroup.mem_sup_right hc.self_mem) hc.sq
    ((Subgroup.mem_normalizer_iff.mp (hnorm hxT) u).mp (Subgroup.mem_zpowers u))
  have hxv : x * v * x⁻¹ = v * e := hc.conj_eq_mul_centralElt hxT hx hxx
    (Subgroup.mem_sup_left hvQ) hvv
    ((Subgroup.mem_normalizer_iff.mp (hTv hxT) v).mp (Subgroup.mem_zpowers v))
  have hvu : v * u = u * v := hc.commute v hvQ u hc.self_mem
  set D := T ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set G) with hD
  have huD : u ∈ D := ⟨hc.right_le hc.self_mem, mem_normalizer_zpowers_of_conj_mem
    (by rw [hc.conj_swap hxu]; exact mul_centralElt_mem_zpowers hxx)⟩
  have hvD : v ∈ D := ⟨hc.left_le hvQ, mem_normalizer_zpowers_of_conj_mem
    (by rw [hc.conj_swap hxv]; exact mul_centralElt_mem_zpowers hxx)⟩
  have hD'X : D.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rintro _ ⟨d, ⟨-, hdN⟩, rfl⟩
    refine mem_normalizer_zpowers_of_conj_mem ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      ((Subgroup.mem_normalizer_iff.mp hdN x).mp (Subgroup.mem_zpowers x))
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hgx, conj_zpow, hk]
    group
  have hD'p : IsPGroup 2 (D.map (MulAut.conj g).toMonoidHom) :=
    (hc.isPGroup.to_le inf_le_left).map _
  obtain ⟨k, hkX, hk⟩ := exists_conj_mem_sylow_of_le S (hST ▸ hnorm) hD'X hD'p
  set σ := MulAut.conj (k * g) with hσ
  have hσT : ∀ d ∈ D, σ d ∈ T := fun d hd => by
    have h1 := hk (g * d * g⁻¹) ⟨d, hd, rfl⟩
    rw [hσ, MulAut.conj_apply, show k * g * d * (k * g)⁻¹ = k * (g * d * g⁻¹) * k⁻¹ by group,
      ← hST]
    exact h1
  have hσe : σ e = e := by rw [hσ, MulAut.conj_apply, hc.conj_centralElt]
  have hx₀ : σ x = u ∨ σ x = u * e := by
    rw [hσ, MulAut.conj_apply, show k * g * x * (k * g)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ by group,
      hgx]
    exact hc.conj_eq_of_mem_zpowers hc.sq
      ((Subgroup.mem_normalizer_iff.mp hkX u).mp (Subgroup.mem_zpowers u))
  have hzz : v * u * (v * u) = 1 := by
    rw [show v * u * (v * u) = v * (u * v) * u by group, ← hvu,
      show v * (v * u) * u = v * v * (u * u) by group, hvv, hc.sq, hc.centralElt_mul_self]
  have hz₁T : σ (v * u) ∈ T := by
    rw [map_mul]
    exact T.mul_mem (hσT v hvD) (hσT u huD)
  have hz₁2 : orderOf (σ (v * u)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hc.orderOf_mul_eq_two hvQ hc.self_mem hvv hc.sq
  have hz₁e : σ (v * u) ≠ e := by
    rw [← hσe, Ne, σ.injective.eq_iff]
    exact hc.mul_ne_centralElt hvQ hc.self_mem hvv
  obtain ⟨q, hq, hqz⟩ := hc.exists_mul_self_of_comm
    (fun p hp p' hp' => comm_right_of_isCyclic hcyc hp hp') hz₁T hz₁2 hz₁e
  have hqu := hc.commute q hq u hc.self_mem
  have hqq : q * q = e := by
    have h1 : q * u * (q * u) = 1 := by rw [← hqz, ← map_mul, hzz, map_one]
    have h2 : q * q * e = 1 := by
      rw [← hc.sq, ← h1, show q * u * (q * u) = q * (u * q) * u by group, ← hqu]
      group
    rw [eq_inv_of_mul_eq_one_left h2, hc.centralElt_inv]
  have hq4 : q = v ∨ q = v * e := by
    by_contra hne
    push Not at hne
    have hq14 := hc.ne_of_mul_self_eq hqq
    have hv₁T := hσT v hvD
    have hv₁z : σ v * σ (v * u) = σ (v * u) * σ v := by
      rw [← map_mul, ← map_mul, show v * (v * u) = v * u * v by
        rw [show v * u * v = v * (u * v) by group, ← hvu]]
    have hq' : q = σ (v * u) * u⁻¹ := by rw [hqz]; group
    have h3 : σ v * q * (σ v)⁻¹ = σ (v * u) * (σ v * u * (σ v)⁻¹)⁻¹ := by
      calc σ v * q * (σ v)⁻¹ = σ v * σ (v * u) * u⁻¹ * (σ v)⁻¹ := by rw [hq']; group
        _ = σ (v * u) * σ v * u⁻¹ * (σ v)⁻¹ := by rw [hv₁z]
        _ = σ (v * u) * (σ v * u * (σ v)⁻¹)⁻¹ := by group
    have hv₁q : σ v * q * (σ v)⁻¹ = q ∨ σ v * q * (σ v)⁻¹ = q * e := by
      rcases hc.conj_eq_of_le_normalizer hc.sq hnorm hv₁T with h | h
      · left
        rw [h3, h, ← hq']
      · right
        rw [h3, h, mul_inv_rev, hc.centralElt_inv, ← mul_assoc, mul_assoc (σ (v * u)) e,
          ← he u⁻¹, ← mul_assoc, ← hq']
    have hv₁s : σ v ∈ Q ⊔ P₁ := by
      by_contra hv₁s
      rcases hc.fix_of_not_mem hyT hy hfix hv₁T hv₁s hq hv₁q with h | h | h | h
      exacts [hq14.1 h, hq14.2 h, hne.1 h, hne.2 h]
    have hv₁u : σ v * u = u * σ v := by
      obtain ⟨q', hq', p', hp', hqp'⟩ := hc.mem_sup_iff.mp hv₁s
      rw [← hqp']
      calc q' * p' * u = q' * (p' * u) := by group
        _ = q' * (u * p') := by rw [comm_right_of_isCyclic hcyc hp' hc.self_mem]
        _ = u * (q' * p') := by rw [← mul_assoc, hc.commute q' hq' u hc.self_mem]; group
    have hσxv : σ x * σ v * (σ x)⁻¹ = σ v * e := by
      rw [← map_inv, ← map_mul, ← map_mul, hxv, map_mul, hσe]
    have hcomm : σ x * σ v = σ v * σ x := by
      rcases hx₀ with h | h <;> rw [h]
      · exact hv₁u.symm
      · calc u * e * σ v = u * (e * σ v) := by group
          _ = u * (σ v * e) := by rw [he]
          _ = σ v * u * e := by rw [← mul_assoc, ← hv₁u]
          _ = σ v * (u * e) := by group
    rw [hcomm, mul_inv_cancel_right] at hσxv
    exact hc.centralElt_ne_one (mul_eq_left.mp hσxv.symm)
  have hσx : ∀ a : G, σ a = k * g * a * (k * g)⁻¹ := fun a => by rw [hσ, MulAut.conj_apply]
  rcases hq4 with h | h
  · refine ⟨k * g, ?_, by rw [← hσx]; exact hx₀⟩
    have h1 : σ (v * u) = v * u := by rw [hqz, h]
    calc k * g * (v * u) = σ (v * u) * (k * g) := by rw [hσx]; group
      _ = v * u * (k * g) := by rw [h1]
  · refine ⟨j * (k * g), ?_, ?_⟩
    · have h1 : σ (v * u) = v * u * e := by rw [hqz, h, mul_assoc v e u, ← he u]; group
      calc j * (k * g) * (v * u) = j * σ (v * u) * j⁻¹ * (j * (k * g)) := by rw [hσx]; group
        _ = v * u * (j * (k * g)) := by
          rw [h1, hc.conj_mul_centralElt, hc.conj_mul_self_of_anticomm hjQ hjv,
            hc.mul_centralElt_mul_centralElt]
    · have hju := hc.commute j hjQ u hc.self_mem
      have h2 : j * (k * g) * x * (j * (k * g))⁻¹ = j * σ x * j⁻¹ := by rw [hσx]; group
      rw [h2]
      rcases hx₀ with h' | h' <;> rw [h']
      · exact Or.inl (by rw [hju, mul_inv_cancel_right])
      · exact Or.inr (by rw [hc.conj_mul_centralElt, hju, mul_inv_cancel_right])

theorem not_mem_of_anticomm (hc : PartC T Q P₁ e u) {v j : G} (hjv : j * v * j⁻¹ = v * e) :
    ¬ (j = 1 ∨ j = e ∨ j = v ∨ j = v * e) := by
  have hne : ∀ w : G, w * v = v * w → j = w → False := fun w hw hjw => by
    rw [hjw, hw, mul_inv_cancel_right] at hjv
    exact hc.centralElt_ne_one (mul_eq_left.mp hjv.symm)
  rintro (h | h | h | h)
  · exact hne 1 (by group) h
  · exact hne e (hc.commute_centralElt v).symm h
  · exact hne v rfl h
  · exact hne (v * e) (by rw [mul_assoc, ← hc.commute_centralElt v, ← mul_assoc]) h

theorem conj_ne_self_of_isCyclic [Finite G] (hc : PartC T Q P₁ e u) (hcyc : IsCyclic P₁)
    (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y = e) (hyi : ∀ p ∈ P₁, y * p * y⁻¹ = p⁻¹) {v : G}
    (hvQ : v ∈ Q) (hvv : v * v = e)
    (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {j : G} (hjQ : j ∈ Q)
    (hjv : j * v * j⁻¹ = v * e) {c : G} (hcP : c ∈ P₁) (hcc : c * c = u ∨ c * c = u * e)
    {x : G} (hxT : x ∈ T) (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) (g : G) : g * x * g⁻¹ ≠ u := by
  intro hgx
  set C := Subgroup.centralizer ({v * u} : Set G) with hC
  set K := ⁅C, C⁆ with hK
  have hz := hc.mul_not_mem_commutator_centralizer hcyc S hST hnorm hyT hy hyy hvQ hvv hTv hjQ
    hjv
  have hCt : ∀ t ∈ T, t ∉ Q ⊔ P₁ → t * t = e → t ∈ C := fun t ht htQ htt =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hc.commute_mul_of_not_mem hnorm hvQ hvv hTv ht htQ htt)
  have hcomm : ∀ t ∈ T, t ∉ Q ⊔ P₁ → t * t = e → ∀ g : G, g * t * g⁻¹ = u →
      u * t⁻¹ ∈ K ∨ u * e * t⁻¹ ∈ K := by
    intro t ht htQ htt g hgt
    obtain ⟨g', hg'z, hg't⟩ := hc.exists_conj_eq_of_conj_eq hcyc S hST hnorm hyT hy hvQ hvv hfix
      hTv hjQ hjv ht htQ htt hgt
    have hmem := Subgroup.commutator_mem_commutator
      (Subgroup.mem_centralizer_singleton_iff.mpr hg'z) (hCt t ht htQ htt)
    rw [commutatorElement_def] at hmem
    rcases hg't with h | h <;> rw [h] at hmem
    · exact Or.inl hmem
    · exact Or.inr hmem
  have hyC := hCt y hyT hy hyy
  have hP₁C : ∀ p ∈ P₁, p ∈ C := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * (v * u) = p * v * u := by group
      _ = v * p * u := by rw [hc.commute v hvQ p hp]
      _ = v * (p * u) := by group
      _ = v * u * p := by rw [comm_right_of_isCyclic hcyc hp hc.self_mem]; group
  have heK : e ∈ K := by
    have h := Subgroup.commutator_mem_commutator (hP₁C u hc.self_mem) hyC
    rwa [commutatorElement_def, show u * y * u⁻¹ * y⁻¹ = u * (y * u * y⁻¹)⁻¹ by group,
      hyi u hc.self_mem, inv_inv, hc.sq] at h
  have huK : u ∈ K := by
    have h := Subgroup.commutator_mem_commutator (hP₁C c hcP) hyC
    rw [commutatorElement_def, show c * y * c⁻¹ * y⁻¹ = c * (y * c * y⁻¹)⁻¹ by group, hyi c hcP,
      inv_inv] at h
    rcases hcc with h' | h' <;> rw [h'] at h
    · exact h
    · have h'' := K.mul_mem h heK
      rwa [hc.mul_centralElt_mul_centralElt] at h''
  have hinvK : ∀ t ∈ T, t ∉ Q ⊔ P₁ → t * t = e → ∀ g : G, g * t * g⁻¹ = u → t⁻¹ ∈ K := by
    intro t ht htQ htt g hgt
    rcases hcomm t ht htQ htt g hgt with h | h
    · have h' := K.mul_mem (K.inv_mem huK) h
      rwa [inv_mul_cancel_left] at h'
    · have h' := K.mul_mem (K.inv_mem (K.mul_mem huK heK)) h
      rwa [inv_mul_cancel_left] at h'
  have hjT : j ∈ T := hc.left_le hjQ
  have hx₂T : j * x * j⁻¹ ∈ T := T.mul_mem (T.mul_mem hjT hxT) (T.inv_mem hjT)
  have hx₂Q : j * x * j⁻¹ ∉ Q ⊔ P₁ := fun h => hx (by
    have h' := hc.conj_mem_sup (T.inv_mem hjT) h
    rwa [show j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x by group] at h')
  have hx₂x₂ : j * x * j⁻¹ * (j * x * j⁻¹) = e := by
    rw [show j * x * j⁻¹ * (j * x * j⁻¹) = j * (x * x) * j⁻¹ by group, hxx, hc.conj_centralElt]
  have hK1 := hinvK x hxT hx hxx g hgx
  have hK2 := hinvK _ hx₂T hx₂Q hx₂x₂ (g * j⁻¹) (by rw [← hgx]; group)
  have hjn := hc.not_mem_of_anticomm hjv
  have hjj : j * j = e :=
    hc.mul_self_of_ne hjQ (fun h => hjn (Or.inl h)) (fun h => hjn (Or.inr (Or.inl h)))
  have hfixx : ∀ w ∈ Q, (x * w * x⁻¹ = w ∨ x * w * x⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e :=
    fun w hw hxw => hc.fix_of_not_mem hyT hy hfix hxT hx hw hxw
  have hj'j' : x * j * x⁻¹ * (x * j * x⁻¹) = e := by
    rw [show x * j * x⁻¹ * (x * j * x⁻¹) = x * (j * j) * x⁻¹ by group, hjj, hc.conj_centralElt]
  have hx₂x : j * x * j⁻¹ * x⁻¹ = j * (x * j * x⁻¹) * e := by
    rw [show j * x * j⁻¹ * x⁻¹ = j * (x * j * x⁻¹)⁻¹ by group, hc.inv_eq_mul_centralElt hj'j']
    group
  have hvK : v ∈ K := by
    have h := K.mul_mem (K.inv_mem hK2) hK1
    rw [inv_inv, hx₂x] at h
    rcases hc.mul_conj_mem hxT (hxx ▸ hc.mem_right) hfixx hjQ with h' | h' | h' | h'
    · exfalso
      refine hjn (hfixx j hjQ (Or.inr ?_))
      calc x * j * x⁻¹ = j⁻¹ * (j * (x * j * x⁻¹)) := by group
        _ = j * e := by rw [h', mul_one, hc.inv_eq_mul_centralElt hjj]
    · exfalso
      refine hjn (hfixx j hjQ (Or.inl ?_))
      calc x * j * x⁻¹ = j⁻¹ * (j * (x * j * x⁻¹)) := by group
        _ = j := by rw [h', hc.inv_eq_mul_centralElt hjj, hc.mul_centralElt_mul_centralElt]
    · rw [h'] at h
      have h'' := K.mul_mem h heK
      rwa [hc.mul_centralElt_mul_centralElt] at h''
    · rwa [h', hc.mul_centralElt_mul_centralElt] at h
  exact hz (K.mul_mem hvK huK)

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
