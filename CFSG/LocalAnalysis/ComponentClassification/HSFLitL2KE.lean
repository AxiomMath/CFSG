module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KThree
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Bar

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Generic

variable {G : Type*} [Group G]

theorem closure_four_eq (a b c d : G) :
    closure ({a, b, c, d} : Set G) = zpowers a ⊔ zpowers b ⊔ zpowers c ⊔ zpowers d := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [zpowers_le] <;>
      exact subset_closure (by simp)

theorem exists_pow_mem_of_mem_sup {P : Subgroup G} {u g : G} (hu : u ^ 2 = 1)
    (hc : P ≤ centralizer ({u} : Set G)) (hg : g ∈ P ⊔ zpowers u) :
    ∃ e : ℕ, e < 2 ∧ g * u ^ e ∈ P := by
  have hN : u ∈ normalizer (P : Set G) := by
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hc ha)
  rcases mem_or_mul_mem_of_mem_sup_zpowers hu hN hg with h | h
  · exact ⟨0, by norm_num, by simpa using h⟩
  · exact ⟨1, by norm_num, by simpa using h⟩

theorem pow_inv_of_sq {u : G} (hu : u ^ 2 = 1) {e : ℕ} (he : e < 2) : (u ^ e)⁻¹ = u ^ e := by
  interval_cases e
  · simp
  · rw [pow_one, inv_eq_iff_mul_eq_one, ← pow_two, hu]

theorem mem_closure_four {a b c d : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hd : d ^ 2 = 1) (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) {g : G}
    (hg : g ∈ closure ({a, b, c, d} : Set G)) :
    ∃ i j k l : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ l < 2 ∧ g = a ^ i * b ^ j * c ^ k * d ^ l := by
  rw [closure_four_eq] at hg
  have mc : ∀ {x y : G}, x * y = y * x → x ∈ centralizer ({y} : Set G) := fun h =>
    mem_centralizer_singleton_iff.mpr h
  obtain ⟨l, hl, hgl⟩ := exists_pow_mem_of_mem_sup hd
    (sup_le (sup_le (zpowers_le.mpr (mc had)) (zpowers_le.mpr (mc hbd))) (zpowers_le.mpr (mc hcd)))
    hg
  obtain ⟨k, hk, hgk⟩ := exists_pow_mem_of_mem_sup hc
    (sup_le (zpowers_le.mpr (mc hac)) (zpowers_le.mpr (mc hbc))) hgl
  obtain ⟨j, hj, hgj⟩ := exists_pow_mem_of_mem_sup hb (zpowers_le.mpr (mc hab)) hgk
  have hi : ∃ i : ℕ, i < 2 ∧ g * d ^ l * c ^ k * b ^ j = a ^ i := by
    rcases eq_one_or_eq_of_mem_zpowers ha hgj with h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  obtain ⟨i, hi, hgi⟩ := hi
  refine ⟨i, j, k, l, hi, hj, hk, hl, ?_⟩
  have hcd' : Commute c d := hcd
  have hbc' : Commute b c := hbc
  have hbd' : Commute b d := hbd
  calc g = g * d ^ l * c ^ k * b ^ j * (b ^ j)⁻¹ * (c ^ k)⁻¹ * (d ^ l)⁻¹ := by group
    _ = a ^ i * b ^ j * c ^ k * d ^ l := by
      rw [hgi, pow_inv_of_sq hb hj, pow_inv_of_sq hc hk, pow_inv_of_sq hd hl]

theorem cycle_of_fpf {V : Subgroup G} {z w d : G} (hz2 : z ^ 2 = 1) (hzw : z * w = w * z)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hwz : w ≠ z)
    (hV : ∀ v, v ∈ V ↔ v = 1 ∨ v = z ∨ v = w ∨ v = z * w)
    (hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V) (hfpf : ∀ v ∈ V, v ≠ 1 → d * v * d⁻¹ ≠ v) :
    (d * z * d⁻¹ = w ∧ d * w * d⁻¹ = z * w) ∨ (d * z * d⁻¹ = z * w ∧ d * w * d⁻¹ = z) := by
  have hzV : z ∈ V := (hV z).mpr (Or.inr (Or.inl rfl))
  have hwV : w ∈ V := (hV w).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hzwV : z * w ∈ V := (hV _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hzinv : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
  have hzw1 : z * w ≠ 1 := fun h => hwz (by
    calc w = z⁻¹ * (z * w) := by group
      _ = z := by rw [h, mul_one, hzinv])
  have hconj1 : ∀ {v : G}, v ≠ 1 → d * v * d⁻¹ ≠ 1 := fun {v} hv h => hv (by
    calc v = d⁻¹ * (d * v * d⁻¹) * d := by group
      _ = 1 := by rw [h]; group)
  have hinj : ∀ {u v : G}, d * u * d⁻¹ = d * v * d⁻¹ → u = v := fun h => by
    simpa using h
  have hmul : ∀ u v : G, d * (u * v) * d⁻¹ = d * u * d⁻¹ * (d * v * d⁻¹) := fun u v => by group
  rcases (hV _).mp (hdV z hzV) with h | h | h | h
  · exact absurd h (hconj1 hz1)
  · exact absurd h (hfpf z hzV hz1)
  · left
    refine ⟨h, ?_⟩
    rcases (hV _).mp (hdV w hwV) with h' | h' | h' | h'
    · exact absurd h' (hconj1 hw1)
    · exfalso
      apply hfpf _ hzwV hzw1
      rw [hmul, h, h', hzw]
    · exact absurd h' (hfpf w hwV hw1)
    · exact h'
  · right
    refine ⟨h, ?_⟩
    rcases (hV _).mp (hdV w hwV) with h' | h' | h' | h'
    · exact absurd h' (hconj1 hw1)
    · exact h'
    · exact absurd h' (hfpf w hwV hw1)
    · exact absurd (hinj (h.trans h'.symm)) hwz.symm

end Generic

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

namespace Gens

variable {C : A.CaseK} (S : Gens A)

theorem z_comm_k (C : A.CaseK) : S.z * C.k = C.k * S.z := (commute_k C S.z_mem).symm

theorem commute_of_mem_T (C : A.CaseK) {g : X} (hg : g ∈ A.T) :
    g * C.k = C.k * g ∧ g * S.z = S.z * g ∧ ∀ w ∈ A.R, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = S.z * w := by
  obtain ⟨r, hr, c, d, -, -, rfl⟩ := exists_eq_of_mem_T C hg
  have hk : ∀ u ∈ A.R, C.k ^ d * u = u * C.k ^ d := fun u hu =>
    ((Commute.pow_left (commute_k C hu) d) : Commute (C.k ^ d) u)
  have ht : ∀ u ∈ centralizer ({t} : Set X), t ^ c * u = u * t ^ c := fun u hu =>
    ((Commute.pow_left (commute_t_of_mem_C hu).symm c) : Commute (t ^ c) u)
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · have h1 : C.k ^ d * C.k = C.k * C.k ^ d := (Commute.pow_left (Commute.refl C.k) d)
    calc r * t ^ c * C.k ^ d * C.k = r * t ^ c * (C.k ^ d * C.k) := by group
      _ = r * (t ^ c * C.k) * C.k ^ d := by rw [h1]; group
      _ = r * C.k * t ^ c * C.k ^ d := by rw [ht C.k (k_mem_C C)]; group
      _ = C.k * (r * t ^ c * C.k ^ d) := by rw [← commute_k C hr]; group
  · have hzC := A.T_le_centralizer S.z_mem.1
    have h1 : C.k ^ d * S.z = S.z * C.k ^ d := hk S.z S.z_mem
    calc r * t ^ c * C.k ^ d * S.z = r * t ^ c * (C.k ^ d * S.z) := by group
      _ = r * (t ^ c * S.z) * C.k ^ d := by rw [h1]; group
      _ = r * S.z * t ^ c * C.k ^ d := by rw [ht S.z hzC]; group
      _ = S.z * (r * t ^ c * C.k ^ d) := by rw [← S.z_comm_R hr]; group
  · have hwC := A.T_le_centralizer hw.1
    have h1 : r * t ^ c * C.k ^ d * w * (r * t ^ c * C.k ^ d)⁻¹ = r * w * r⁻¹ := by
      calc r * t ^ c * C.k ^ d * w * (r * t ^ c * C.k ^ d)⁻¹
          = r * t ^ c * (C.k ^ d * w) * (C.k ^ d)⁻¹ * (t ^ c)⁻¹ * r⁻¹ := by group
        _ = r * (t ^ c * w) * (t ^ c)⁻¹ * r⁻¹ := by rw [hk w hw]; group
        _ = r * w * r⁻¹ := by rw [ht w hwC]; group
    rw [h1]
    rcases S.comm_mem_R hr hw with h | h
    · left
      calc r * w * r⁻¹ = r * w * r⁻¹ * w⁻¹ * w := by group
        _ = w := by rw [h, one_mul]
    · right
      calc r * w * r⁻¹ = r * w * r⁻¹ * w⁻¹ * w := by group
        _ = S.z * w := by rw [h]

theorem mem_L2E (C : A.CaseK) {w : X} (hw : w ∈ A.R) (hw2 : w ^ 2 = 1) {g : X}
    (hg : g ∈ L2E S.z w t C.k) :
    ∃ a b c d : ℕ, a < 2 ∧ b < 2 ∧ c < 2 ∧ d < 2 ∧ g = S.z ^ a * w ^ b * t ^ c * C.k ^ d := by
  have hzC := A.T_le_centralizer S.z_mem.1
  have hwC := A.T_le_centralizer hw.1
  exact mem_closure_four S.z_sq hw2 (t_sq (A := A)) C.k_sq (S.z_comm_R hw)
    (commute_t_of_mem_C hzC) (S.z_comm_k C) (commute_t_of_mem_C hwC) (commute_k C hw).symm
    (commute_t_of_mem_C (k_mem_C C)).symm hg

omit [Finite X] in
theorem z_mem_L2E (C : A.CaseK) (w : X) : S.z ∈ L2E S.z w t C.k := subset_closure (by simp)

omit [Finite X] in
theorem w_mem_L2E (C : A.CaseK) (w : X) : w ∈ L2E S.z w t C.k := subset_closure (by simp)

omit [Finite X] in
theorem t_mem_L2E (C : A.CaseK) (w : X) : t ∈ L2E S.z w t C.k := subset_closure (by simp)

omit [Finite X] in
theorem k_mem_L2E (C : A.CaseK) (w : X) : C.k ∈ L2E S.z w t C.k := subset_closure (by simp)

theorem T_le_normalizer_L2E (C : A.CaseK) {w : X} (hw : w ∈ A.R) :
    A.T ≤ normalizer (L2E S.z w t C.k : Set X) := by
  intro g hg
  obtain ⟨hgk, hgz, hgw⟩ := S.commute_of_mem_T C hg
  refine mem_normalizer_of_conj_mem fun e he => ?_
  have hle : L2E S.z w t C.k ≤ (L2E S.z w t C.k).comap (MulAut.conj g).toMonoidHom := by
    rw [L2E, closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hs with rfl | rfl | rfl | rfl
    · rw [hgz, mul_inv_cancel_right]
      exact S.z_mem_L2E C w
    · rcases hgw s hw with h | h <;> rw [h]
      · exact S.w_mem_L2E C s
      · exact mul_mem (S.z_mem_L2E C s) (S.w_mem_L2E C s)
    · rw [commute_t_of_mem_C (A.T_le_centralizer hg), mul_inv_cancel_right]
      exact S.t_mem_L2E C w
    · rw [hgk, mul_inv_cancel_right]
      exact S.k_mem_L2E C w
  exact hle he

theorem mem_L2E_of_mem_L (C : A.CaseK) {w : X} (hw : w ∈ A.R) (hw2 : w ^ 2 = 1) {g : X}
    (hg : g ∈ L2E S.z w t C.k) (hgL : g ∈ L) :
    ∃ a b : ℕ, a < 2 ∧ b < 2 ∧ g = S.z ^ a * w ^ b := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := S.mem_L2E C hw hw2 hg
  have hzwL : S.z ^ a * w ^ b ∈ L := mul_mem (pow_mem S.z_mem.2 a) (pow_mem hw.2 b)
  have htk : t ^ c * C.k ^ d ∈ L := by
    have := mul_mem (inv_mem hzwL) hgL
    simpa [mul_assoc] using this
  have htkT : t ^ c * C.k ^ d ∈ A.T := mul_mem (pow_mem A.t_mem_T c) (pow_mem C.k_mem d)
  have hd0 : d = 0 := by
    by_contra hd0
    have hd1 : d = 1 := by omega
    subst hd1
    have hψ := ψX_mem_R8 (A := A) ⟨htkT, htk⟩
    rw [ψX_mul (pow_mem A.t_mem_T c) (pow_mem C.k_mem 1), ψX_pow A.t_mem_T, ψX_t, one_pow,
      one_mul, pow_one, ψX_k C] at hψ
    exact k8_not_mem_R8 hψ
  subst hd0
  have hc0 : c = 0 := by
    by_contra hc0
    have hc1 : c = 1 := by omega
    subst hc1
    rw [pow_one, pow_zero, mul_one] at htk
    exact A.config.not_mem htk
  subst hc0
  exact ⟨a, b, ha, hb, by simp⟩

end Gens

namespace Frame

variable {C : A.CaseK} {κ : X} (Fr : Frame A F κ)

theorem right_act_of_mem_R {r : X} (hr : r ∈ A.R) : (act A Fr.e r).right = 1 := by
  rw [act_of_mem_L Fr.e hr.2]
  rfl

theorem right_act_k (S : Gens A) (C : A.CaseK) (hκ : κ = C.k ∨ κ = S.z * C.k) :
    (act A Fr.e C.k).right = Fr.σ := by
  rcases hκ with rfl | rfl
  · rw [Fr.act_κ]
    rfl
  · have hzC := A.T_le_centralizer S.z_mem.1
    have h : act A Fr.e C.k = (act A Fr.e S.z)⁻¹ * act A Fr.e (S.z * C.k) := by
      rw [act_mul Fr.e hzC (k_mem_C C), inv_mul_cancel_left]
    rw [h, Fr.act_κ, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      Fr.right_act_of_mem_R S.z_mem, inv_one, one_mul]
    rfl

theorem conj_eq_or_of_mem_L2E (S : Gens A) (C : A.CaseK) (hκ : κ = C.k ∨ κ = S.z * C.k)
    {w : X} (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) {n : X} (hn : n ∈ centralizer ({t} : Set X))
    (hnE : n * κ * n⁻¹ ∈ L2E S.z w t C.k) : n * κ * n⁻¹ = κ ∨ n * κ * n⁻¹ = t * κ := by
  have hwR := Fr.V_le_R hwV
  obtain ⟨a, b, c, d, ha, hb, hc, hd, habcd⟩ := S.mem_L2E C hwR hw2 hnE
  have hzC := A.T_le_centralizer S.z_mem.1
  have hwC := A.T_le_centralizer hwR.1
  have hkC := k_mem_C C
  have hσ1 : Fr.σ ≠ 1 := by
    intro h
    have := Fr.orderOf_σ
    rw [h, orderOf_one] at this
    norm_num at this
  have hd1 : d = 1 := by
    have h1 := congrArg (fun g => (act A Fr.e g).right) habcd
    rw [act_conj Fr.e hn Fr.κ_C, right_conj, Fr.act_κ,
      act_mul Fr.e (mul_mem (mul_mem (pow_mem hzC a) (pow_mem hwC b)) (pow_mem t_mem_C c))
        (pow_mem hkC d),
      act_mul Fr.e (mul_mem (pow_mem hzC a) (pow_mem hwC b)) (pow_mem t_mem_C c),
      act_mul Fr.e (pow_mem hzC a) (pow_mem hwC b), act_pow Fr.e hzC, act_pow Fr.e hwC,
      act_pow Fr.e t_mem_C, act_pow Fr.e hkC, act_t, one_pow, mul_one] at h1
    change Fr.σ = (fieldProj F) (act A Fr.e S.z ^ a * act A Fr.e w ^ b * act A Fr.e C.k ^ d)
      at h1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow] at h1
    change Fr.σ = (act A Fr.e S.z).right ^ a * (act A Fr.e w).right ^ b *
      (act A Fr.e C.k).right ^ d at h1
    rw [Fr.right_act_of_mem_R S.z_mem, Fr.right_act_of_mem_R hwR, Fr.right_act_k S C hκ, one_pow,
      one_pow, one_mul, one_mul] at h1
    by_contra hd1
    have hd0 : d = 0 := by omega
    rw [hd0, pow_zero] at h1
    exact hσ1 h1
  subst hd1
  have hzV := Fr.z_mem_V S
  have hzt : S.z * t = t * S.z := commute_t_of_mem_C hzC
  obtain ⟨v, hvV, hv⟩ : ∃ v ∈ Fr.V, n * κ * n⁻¹ = v * t ^ c * κ := by
    rw [habcd, pow_one]
    rcases hκ with h | h
    · exact ⟨S.z ^ a * w ^ b, mul_mem (pow_mem hzV a) (pow_mem hwV b), by rw [h]⟩
    · refine ⟨S.z ^ a * w ^ b * S.z, mul_mem (mul_mem (pow_mem hzV a) (pow_mem hwV b)) hzV, ?_⟩
      rw [h]
      have htc : S.z * t ^ c = t ^ c * S.z := (Commute.pow_right hzt c)
      calc S.z ^ a * w ^ b * t ^ c * C.k = S.z ^ a * w ^ b * (S.z * S.z) * t ^ c * C.k := by
            rw [← pow_two, S.z_sq, mul_one]
        _ = S.z ^ a * w ^ b * S.z * (S.z * t ^ c) * C.k := by group
        _ = S.z ^ a * w ^ b * S.z * t ^ c * (S.z * C.k) := by rw [htc]; group
  have hv1 := Fr.eq_one_of_conj C S hn hvV c hv
  rw [hv1, one_mul] at hv
  interval_cases c
  · left
    rw [hv, pow_zero, one_mul]
  · right
    rw [hv, pow_one]

theorem conj_eq_of_mem_normalizer (S : Gens A) (C : A.CaseK) (hκ : κ = C.k ∨ κ = S.z * C.k)
    {w : X} (hwV : w ∈ Fr.V) (hw2 : w ^ 2 = 1) {n : X}
    (hn : n ∈ normalizer (L2E S.z w t C.k : Set X) ⊓ centralizer ({t} : Set X)) :
    n * κ * n⁻¹ = κ := by
  have hwR := Fr.V_le_R hwV
  have hκE : κ ∈ L2E S.z w t C.k := by
    rcases hκ with rfl | rfl
    · exact S.k_mem_L2E C w
    · exact mul_mem (S.z_mem_L2E C w) (S.k_mem_L2E C w)
  refine conj_eq_of_mem_pair (A := A) (le_inf (S.T_le_normalizer_L2E C hwR) A.T_le_centralizer)
    inf_le_right (fun g hg => ?_) (fun m hm => ?_) hn
  · rw [mem_centralizer_singleton_iff]
    obtain ⟨hgk, hgz, -⟩ := S.commute_of_mem_T C hg
    rcases hκ with rfl | rfl
    · exact hgk
    · calc g * (S.z * C.k) = S.z * (g * C.k) := by rw [← mul_assoc, hgz, mul_assoc]
        _ = S.z * C.k * g := by rw [hgk, mul_assoc]
  · exact Fr.conj_eq_or_of_mem_L2E S C hκ hwV hw2 hm.2
      ((mem_normalizer_iff.mp hm.1 κ).mp hκE)

theorem exists_cycle (S : Gens A) {w : X}
    (hV : ∀ v, v ∈ Fr.V ↔ v = 1 ∨ v = S.z ∨ v = w ∨ v = S.z * w) (hw1 : w ≠ 1) (hwz : w ≠ S.z)
    (hzw : S.z * w = w * S.z) :
    ∃ d ∈ L, d * κ = κ * d ∧ d * S.z * d⁻¹ = w ∧ d * w * d⁻¹ = S.z * w := by
  obtain ⟨d, hdL, hdκ, hdV, hfpf⟩ := Fr.exists_three S
  have hz2 := S.z_sq
  have hzinv : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2]
  rcases cycle_of_fpf hz2 hzw S.z_ne_one hw1 hwz hV hdV hfpf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨d, hdL, hdκ, h1, h2⟩
  · refine ⟨d⁻¹, inv_mem hdL, ?_, ?_, ?_⟩
    · calc d⁻¹ * κ = d⁻¹ * (κ * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * κ) * d⁻¹ := by rw [hdκ]
        _ = κ * d⁻¹ := by group
    · calc d⁻¹ * S.z * d⁻¹⁻¹ = d⁻¹ * (d * w * d⁻¹) * d := by rw [h2]; group
        _ = w := by group
    · have h3 : d * (S.z * w) * d⁻¹ = w := by
        calc d * (S.z * w) * d⁻¹ = (d * S.z * d⁻¹) * (d * w * d⁻¹) := by group
          _ = S.z * w * S.z := by rw [h1, h2]
          _ = w := by rw [mul_assoc, ← hzw, ← mul_assoc, ← pow_two, hz2, one_mul]
      calc d⁻¹ * w * d⁻¹⁻¹ = d⁻¹ * (d * (S.z * w) * d⁻¹) * d := by rw [h3]; group
        _ = S.z * w := by group

end Frame

end CFSG.ComponentClassification.HSFLit.L2K
