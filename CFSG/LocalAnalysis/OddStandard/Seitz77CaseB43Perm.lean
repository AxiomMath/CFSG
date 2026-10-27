module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseBasic
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Main
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Symm

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G}

theorem CaseB.Factors.symm (F : c.Factors M₁ M₂) : c.Factors M₂ M₁ where
  ninf_eq := by rw [F.ninf_eq, sup_comm]
  perfect₁ := F.perfect₂
  perfect₂ := F.perfect₁
  norm₁ := F.norm₂
  norm₂ := F.norm₁
  odd_inf := by rw [inf_comm]; exact F.odd_inf
  comm_eq_bot := fun hZ => by rw [Subgroup.commutator_comm]; exact F.comm_eq_bot hZ
  swap₁ := F.swap₂
  swap₂ := F.swap₁
  W_le := F.W_le
  card₁ := F.card₂
  card₂ := F.card₁
  W_eq := by rw [sup_comm]; exact F.W_eq
  W_disj := by rw [inf_comm]; exact F.W_disj
  W₂_cent := F.W₁_cent
  W₁_cent := F.W₂_cent
  irr₁ := F.irr₂
  irr₂ := F.irr₁
  faithful₁ := F.faithful₂
  faithful₂ := F.faithful₁
  fpf₁ := F.fpf₂
  fpf₂ := F.fpf₁
  a5₁ := F.a5₂
  a5₂ := F.a5₁
  card_M₁ := F.card_M₂
  card_M₂ := F.card_M₁
  sylow_card₁ := F.sylow_card₂
  sylow_card₂ := F.sylow_card₁
  sylow_W₁ := F.sylow_W₂
  sylow_W₂ := F.sylow_W₁
  two_elem := F.two_elem
  exists_O₁ := F.exists_O₁

end Symm

section MinInv

variable {G : Type} [Group G]

theorem cs_bot' (g : G) : CaseB45.cs g (⊥ : Subgroup G) = ⊥ := Subgroup.map_bot _

structure MinInv (H F : Subgroup G) : Prop where
  ne_bot : F ≠ ⊥
  inv : ∀ n ∈ H, ∀ f ∈ F, n * f * n⁻¹ ∈ F
  min : ∀ V : Subgroup G, V ≤ F → (∀ n ∈ H, ∀ v ∈ V, n * v * n⁻¹ ∈ V) → V = ⊥ ∨ V = F

theorem MinInv.cs {H F : Subgroup G} (hF : MinInv H F) {y : G} (hy : CaseB45.cs y H = H) :
    MinInv H (CaseB45.cs y F) := by
  have hmemH : ∀ n, n ∈ H ↔ y⁻¹ * n * y ∈ H := fun n => by
    rw [← mem_cs, hy]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hF.ne_bot
    have h' : CaseB45.cs y⁻¹ (CaseB45.cs y F) = CaseB45.cs y⁻¹ ⊥ := by rw [h]
    rw [cs_inv_cs, cs_bot'] at h'
    exact h'
  
  · intro n hn f hf
    rw [mem_cs] at hf ⊢
    have e : y⁻¹ * (n * f * n⁻¹) * y = (y⁻¹ * n * y) * (y⁻¹ * f * y) * (y⁻¹ * n * y)⁻¹ := by
      group
    rw [e]
    exact hF.inv _ ((hmemH n).mp hn) _ hf
  · intro V hVF hVinv
    have hV' : CaseB45.cs y⁻¹ V ≤ F := by
      have := cs_mono y⁻¹ hVF
      rwa [cs_inv_cs] at this
    have hinv' : ∀ n ∈ H, ∀ v ∈ CaseB45.cs y⁻¹ V, n * v * n⁻¹ ∈ CaseB45.cs y⁻¹ V := by
      intro n hn v hv
      rw [mem_cs] at hv ⊢
      have e : y⁻¹⁻¹ * (n * v * n⁻¹) * y⁻¹ =
          (y⁻¹⁻¹ * n * y⁻¹) * (y⁻¹⁻¹ * v * y⁻¹) * (y⁻¹⁻¹ * n * y⁻¹)⁻¹ := by group
      rw [e]
      refine hVinv _ ?_ _ hv
      rw [hmemH]
      have e2 : y⁻¹ * (y⁻¹⁻¹ * n * y⁻¹) * y = n := by group
      rw [e2]
      exact hn
    rcases hF.min _ hV' hinv' with h | h
    · left
      have h' : CaseB45.cs y (CaseB45.cs y⁻¹ V) = CaseB45.cs y ⊥ := by rw [h]
      rwa [cs_cs_inv, cs_bot'] at h'
    · right
      have h' : CaseB45.cs y (CaseB45.cs y⁻¹ V) = CaseB45.cs y F := by rw [h]
      rwa [cs_cs_inv] at h'

end MinInv

section Fac

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G} (F : c.Factors M₁ M₂)

include F

theorem CaseB.Factors.M₁_le : M₁ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_left

theorem CaseB.Factors.M₂_le : M₂ ≤ c.Ninf := by rw [F.ninf_eq]; exact le_sup_right

theorem CaseB.Factors.minInv_F₁ : MinInv c.Ninf (c.W ⊓ M₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := F.card₁
    rw [h, Subgroup.card_bot] at this
    omega
  · intro n hn f hf
    have hnN : n ∈ c.N := prOf_le c.N hn
    exact ⟨(mem_normalizer_iff.mp hnN f).mp hf.1, F.norm₁ n hn f hf.2⟩
  · intro V hVF hVinv
    exact F.irr₁ V hVF (fun m hm v hv => hVinv m (F.M₁_le hm) v hv)

omit F in
theorem cs_Ninf_eq {y : G} (hy : y ∈ c.N) : CaseB45.cs y c.Ninf = c.Ninf := by
  ext x
  rw [mem_cs]
  constructor
  · intro hx
    have := prOf_conj_mem c.N hy hx
    simpa [mul_assoc] using this
  · intro hx
    have := prOf_conj_mem c.N (c.N.inv_mem hy) hx
    simpa using this

omit F in
theorem cs_W_eq {y : G} (hy : y ∈ c.N) : CaseB45.cs y c.W = c.W := by
  ext x
  rw [mem_cs]
  have h1 := mem_normalizer_iff.mp (c.N.inv_mem hy) x
  constructor
  · intro hx
    have := (mem_normalizer_iff.mp hy (y⁻¹ * x * y)).mp hx
    simpa [mul_assoc] using this
  · intro hx
    have := (mem_normalizer_iff.mp (c.N.inv_mem hy) x).mp hx
    simpa using this

theorem CaseB.Factors.cent_F₂ {f : G} (hf : f ∈ c.W ⊓ M₂) (hcent : ∀ m ∈ M₂, m * f * m⁻¹ = f) :
    f = 1 := by
  set C₂ : Subgroup G := (c.W ⊓ M₂) ⊓ centralizer (M₂ : Set G) with hC₂
  have hinv : ∀ m ∈ M₂, ∀ v ∈ C₂, m * v * m⁻¹ ∈ C₂ := by
    intro m hm v hv
    have : m * v * m⁻¹ = v := by
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_iff.mp hv.2 m hm
    rw [this]
    exact hv
  rcases F.irr₂ C₂ inf_le_left hinv with h | h
  · have hfC : f ∈ C₂ := ⟨hf, mem_centralizer_iff.mpr fun m hm => by
      have := hcent m hm
      calc m * f = m * f * m⁻¹ * m := by group
        _ = f * m := by rw [this]⟩
    rw [h, Subgroup.mem_bot] at hfC
    exact hfC
  · exfalso
    have hle : M₂ ≤ centralizer (c.W : Set G) := by
      intro m hm
      refine F.faithful₂ m hm fun w hw => ?_
      have hwC : w ∈ C₂ := by rw [h]; exact hw
      have := mem_centralizer_iff.mp hwC.2 m hm
      calc m * w * m⁻¹ = w * m * m⁻¹ := by rw [this]
        _ = w := by group
    have hcard := F.card_M₂
    rw [inf_eq_left.mpr hle] at hcard
    have hpos : 0 < Nat.card ↥M₂ := Nat.card_pos
    omega

theorem CaseB.Factors.cent_F₁ {f : G} (hf : f ∈ c.W ⊓ M₁) (hcent : ∀ m ∈ M₁, m * f * m⁻¹ = f) :
    f = 1 :=
  F.symm.cent_F₂ hf hcent

theorem CaseB.Factors.part₂ {U : Subgroup G} (hU : MinInv c.Ninf U)
    (hU2 : U ⊓ (c.W ⊓ M₂) = ⊥) {f₁ f₂ : G} (hf₁ : f₁ ∈ c.W ⊓ M₁) (hf₂ : f₂ ∈ c.W ⊓ M₂)
    (hu : f₁ * f₂ ∈ U) : f₂ = 1 := by
  have hF₂ := F.symm.minInv_F₁
  have hcent : ∀ m ∈ M₂, m * f₂ * m⁻¹ = f₂ := by
    intro m hm
    have hmN : m ∈ c.Ninf := F.M₂_le hm
    have h1 : m * (f₁ * f₂) * m⁻¹ ∈ U := hU.inv m hmN _ hu
    have hfm : m * f₁ = f₁ * m := mem_centralizer_iff.mp (F.W₁_cent hf₁) m hm
    have hfm' : m * f₁ * m⁻¹ = f₁ := by rw [hfm]; group
    have hz2 : (m * f₂ * m⁻¹) * f₂⁻¹ ∈ c.W ⊓ M₂ :=
      (c.W ⊓ M₂).mul_mem (hF₂.inv m hmN f₂ hf₂) ((c.W ⊓ M₂).inv_mem hf₂)
    have hcommz : f₁ * ((m * f₂ * m⁻¹) * f₂⁻¹) = ((m * f₂ * m⁻¹) * f₂⁻¹) * f₁ :=
      comm_of_isElemAbelian_two c.W_elem hf₁.1 hz2.1
    have hzU : (m * f₂ * m⁻¹) * f₂⁻¹ ∈ U := by
      have h2 := U.mul_mem h1 (U.inv_mem hu)
      have e : m * (f₁ * f₂) * m⁻¹ * (f₁ * f₂)⁻¹ = (m * f₂ * m⁻¹) * f₂⁻¹ := by
        calc m * (f₁ * f₂) * m⁻¹ * (f₁ * f₂)⁻¹
            = (m * f₁ * m⁻¹) * (m * f₂ * m⁻¹) * f₂⁻¹ * f₁⁻¹ := by group
          _ = f₁ * ((m * f₂ * m⁻¹) * f₂⁻¹) * f₁⁻¹ := by rw [hfm']; group
          _ = (m * f₂ * m⁻¹) * f₂⁻¹ := by rw [hcommz]; group
      rwa [e] at h2
    have hz1 : (m * f₂ * m⁻¹) * f₂⁻¹ ∈ U ⊓ (c.W ⊓ M₂) := ⟨hzU, hz2⟩
    rw [hU2, Subgroup.mem_bot] at hz1
    exact mul_inv_eq_one.mp hz1
  exact F.cent_F₂ hf₂ hcent

theorem CaseB.Factors.eq_F₁_or_F₂ {U : Subgroup G} (hU : MinInv c.Ninf U) (hUW : U ≤ c.W) :
    U = c.W ⊓ M₁ ∨ U = c.W ⊓ M₂ := by
  have hF₁ := F.minInv_F₁
  have hF₂ := F.symm.minInv_F₁
  have hI₂ : U ⊓ (c.W ⊓ M₂) = ⊥ ∨ U ⊓ (c.W ⊓ M₂) = U :=
    hU.min _ inf_le_left (fun n hn v hv => ⟨hU.inv n hn v hv.1, hF₂.inv n hn v hv.2⟩)
  have hI₁ : U ⊓ (c.W ⊓ M₁) = ⊥ ∨ U ⊓ (c.W ⊓ M₁) = U :=
    hU.min _ inf_le_left (fun n hn v hv => ⟨hU.inv n hn v hv.1, hF₁.inv n hn v hv.2⟩)
  by_cases h2 : U ⊓ (c.W ⊓ M₂) = U
  · right
    have hUF₂ : U ≤ c.W ⊓ M₂ := by
      conv_lhs => rw [← h2]
      exact inf_le_right
    rcases hF₂.min U hUF₂ hU.inv with h | h
    · exact absurd h hU.ne_bot
    · exact h
  · have h2' : U ⊓ (c.W ⊓ M₂) = ⊥ := hI₂.resolve_right h2
    by_cases h1 : U ⊓ (c.W ⊓ M₁) = U
    · left
      have hUF₁ : U ≤ c.W ⊓ M₁ := by
        conv_lhs => rw [← h1]
        exact inf_le_right
      rcases hF₁.min U hUF₁ hU.inv with h | h
      · exact absurd h hU.ne_bot
      · exact h
    · have h1' : U ⊓ (c.W ⊓ M₁) = ⊥ := hI₁.resolve_right h1
      exfalso
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hU.ne_bot (eq_bot_iff.mpr fun x hx => by rw [hcon x hx]; exact one_mem _)
      have huW := hUW hu
      rw [← F.W_eq] at huW
      obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := mem_sup_of_forall_comm (O := c.W ⊓ M₁) (E := c.W ⊓ M₂)
        (fun x hx y hy => comm_of_isElemAbelian_two c.W_elem hx.1 hy.1) huW
      have hf₂1 := F.part₂ hU h2' hf₁ hf₂ hu
      have hu' : f₂ * f₁ ∈ U := by
        rwa [comm_of_isElemAbelian_two c.W_elem hf₂.1 hf₁.1]
      have hf₁1 := F.symm.part₂ hU h1' hf₂ hf₁ hu'
      exact hu1 (by rw [hf₁1, hf₂1, one_mul])

omit F [Finite G] in
theorem cs_pow_fixed {H : Subgroup G} {g : G} (h : CaseB45.cs g H = H) (n : ℕ) :
    CaseB45.cs (g ^ n) H = H := by
  induction n with
  | zero => rw [pow_zero, cs_one]
  | succ n ih => rw [pow_succ, cs_mul, h, ih]

theorem CaseB.Factors.cs_F₁_of_odd {y : G} (hy : y ∈ c.N) (hodd : Odd (orderOf y)) :
    CaseB45.cs y (c.W ⊓ M₁) = c.W ⊓ M₁ := by
  have hN := cs_Ninf_eq (c := c) hy
  have hF₁ := F.minInv_F₁
  have hF₂ := F.symm.minInv_F₁
  have hne : c.W ⊓ M₁ ≠ c.W ⊓ M₂ := by
    intro h
    have := F.W_disj
    rw [h, inf_idem] at this
    exact hF₂.ne_bot this
  have hle₁ : CaseB45.cs y (c.W ⊓ M₁) ≤ c.W :=
    (cs_mono y inf_le_left).trans (cs_W_eq (c := c) hy).le
  have hle₂ : CaseB45.cs y (c.W ⊓ M₂) ≤ c.W :=
    (cs_mono y inf_le_left).trans (cs_W_eq (c := c) hy).le
  rcases F.eq_F₁_or_F₂ (hF₁.cs hN) hle₁ with h1 | h1
  · exact h1
  · exfalso
    rcases F.eq_F₁_or_F₂ (hF₂.cs hN) hle₂ with h2 | h2
    ·
      have hyy : CaseB45.cs (y * y) (c.W ⊓ M₁) = c.W ⊓ M₁ := by
        rw [cs_mul, h1, h2]
      obtain ⟨n, hn⟩ := hodd
      have hpow : y ^ (2 * n + 1) = 1 := by rw [← hn]; exact pow_orderOf_eq_one y
      have hy_eq : y = (y * y) ^ (n + 1) := by
        calc y = y * y ^ (2 * n + 1) := by rw [hpow, mul_one]
          _ = (y * y) ^ (n + 1) := by rw [← pow_succ', ← sq, ← pow_mul]; ring_nf
      have hfix := cs_pow_fixed hyy (n + 1)
      rw [← hy_eq, h1] at hfix
      exact hne hfix.symm
    · apply hne
      have := congrArg (CaseB45.cs y⁻¹) (h1.trans h2.symm)
      rwa [cs_inv_cs, cs_inv_cs] at this

theorem CaseB.Factors.cs_F₂_of_odd {y : G} (hy : y ∈ c.N) (hodd : Odd (orderOf y)) :
    CaseB45.cs y (c.W ⊓ M₂) = c.W ⊓ M₂ :=
  F.symm.cs_F₁_of_odd hy hodd

theorem CaseB.Factors.comm_mem_M₁ (hZ : c.OddCoreCentral) {p p' : G} (hp : p ∈ c.Ninf)
    (hp' : p' ∈ c.Ninf) (hpC : ∀ f ∈ c.W ⊓ M₂, p * f = f * p)
    (hpC' : ∀ f ∈ c.W ⊓ M₂, p' * f = f * p') : ⁅p, p'⁆ ∈ M₁ := by
  have hcomm : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := fun x hx y hy => F.comm_elem hZ hx hy
  obtain ⟨m, hm, a, ha, rfl⟩ := mem_sup_of_forall_comm (O := M₁) (E := M₂) hcomm
    (F.ninf_eq ▸ hp)
  obtain ⟨m', hm', a', ha', rfl⟩ := mem_sup_of_forall_comm (O := M₁) (E := M₂) hcomm
    (F.ninf_eq ▸ hp')
  have hcen : ∀ (m a : G), m ∈ M₁ → a ∈ M₂ → (∀ f ∈ c.W ⊓ M₂, (m * a) * f = f * (m * a)) →
      a ∈ centralizer (c.W : Set G) := by
    intro m a hm ha hpC
    refine F.faithful₂ a ha fun w hw => ?_
    have hmf : m * w = w * m := mem_centralizer_iff.mp (F.W₂_cent hw) m hm
    have hmf' : m⁻¹ * w * m = w := by
      calc m⁻¹ * w * m = m⁻¹ * (w * m) := by group
        _ = m⁻¹ * (m * w) := by rw [hmf]
        _ = w := by group
    have : a * w = w * a := by
      calc a * w = m⁻¹ * ((m * a) * w) := by group
        _ = m⁻¹ * (w * (m * a)) := by rw [hpC w hw]
        _ = (m⁻¹ * w * m) * a := by group
        _ = w * a := by rw [hmf']
    calc a * w * a⁻¹ = w * a * a⁻¹ := by rw [this]
      _ = w := by group
  have haC := hcen m a hm ha hpC
  have ha'C := hcen m' a' hm' ha' hpC'
  have haa' : a * a' = a' * a := by
    obtain ⟨O₁, hO₁C, hO₁odd, -, hO₁dec, hO₁norm, -⟩ := F.exists_O₁
    obtain ⟨w, hw, o, ho, rfl⟩ := hO₁dec a haC
    obtain ⟨w', hw', o', ho', rfl⟩ := hO₁dec a' ha'C
    have hoN : o ∈ c.Ninf := by
      have := c.Ninf.mul_mem (c.Ninf.inv_mem (F.W_le hw)) (F.M₂_le ha)
      simpa using this
    have ho'N : o' ∈ c.Ninf := by
      have := c.Ninf.mul_mem (c.Ninf.inv_mem (F.W_le hw')) (F.M₂_le ha')
      simpa using this
    have hodd : Odd (Nat.card ↥(O₁ ⊓ c.Ninf)) :=
      hO₁odd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hoo' : o * o' = o' * o :=
      hZ (O₁ ⊓ c.Ninf) inf_le_right (fun n hn q hq =>
        ⟨hO₁norm n hn q hq.1, c.Ninf.mul_mem (c.Ninf.mul_mem hn hq.2) (c.Ninf.inv_mem hn)⟩)
        hodd o ⟨ho, hoN⟩ o' ho'N
    have hww' : w * w' = w' * w := comm_of_isElemAbelian_two c.W_elem hw hw'
    have how' : o * w' = w' * o := (mem_centralizer_iff.mp (hO₁C ho) w' hw').symm
    have ho'w : o' * w = w * o' := (mem_centralizer_iff.mp (hO₁C ho') w hw).symm
    calc w * o * (w' * o') = w * (o * w') * o' := by group
      _ = w * (w' * o) * o' := by rw [how']
      _ = (w * w') * (o * o') := by group
      _ = (w' * w) * (o' * o) := by rw [hww', hoo']
      _ = w' * (w * o') * o := by group
      _ = w' * (o' * w) * o := by rw [← ho'w]
      _ = w' * o' * (w * o) := by group
  have h1 : (m * a) * (m' * a') = (m * m') * (a * a') := by
    calc (m * a) * (m' * a') = m * (a * m') * a' := by group
      _ = m * (m' * a) * a' := by rw [← hcomm m' hm' a ha]
      _ = (m * m') * (a * a') := by group
  have h2 : (m' * a') * (m * a) = (m' * m) * (a' * a) := by
    calc (m' * a') * (m * a) = m' * (a' * m) * a := by group
      _ = m' * (m * a') * a := by rw [← hcomm m hm a' ha']
      _ = (m' * m) * (a' * a) := by group
  have e : ⁅m * a, m' * a'⁆ = (m * m') * (m' * m)⁻¹ := by
    calc ⁅m * a, m' * a'⁆ = ((m * a) * (m' * a')) * ((m' * a') * (m * a))⁻¹ := by
          rw [commutatorElement_def]; group
      _ = ((m * m') * (a * a')) * ((m' * m) * (a' * a))⁻¹ := by rw [h1, h2]
      _ = ((m * m') * (a' * a)) * ((m' * m) * (a' * a))⁻¹ := by rw [haa']
      _ = (m * m') * (m' * m)⁻¹ := by group
  rw [e]
  exact M₁.mul_mem (M₁.mul_mem hm hm') (M₁.inv_mem (M₁.mul_mem hm' hm))

theorem CaseB.Factors.perf_le_M₁ (hZ : c.OddCoreCentral) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPN : P ≤ c.Ninf) (hPC : ∀ p ∈ P, ∀ f ∈ c.W ⊓ M₂, p * f = f * p) : P ≤ M₁ := by
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ M₁ := by
      rw [Subgroup.commutator_le]
      intro p hp p' hp'
      exact F.comm_mem_M₁ hZ (hPN hp) (hPN hp') (hPC p hp) (hPC p' hp')

theorem CaseB.Factors.conj_mem_of_odd (hZ : c.OddCoreCentral) {y : G} (hy : y ∈ c.N)
    (hodd : Odd (orderOf y)) {m : G} (hm : m ∈ M₁) : y * m * y⁻¹ ∈ M₁ := by
  have hF₂ := F.cs_F₂_of_odd hy hodd
  have hperf : ⁅CaseB45.cs y M₁, CaseB45.cs y M₁⁆ = CaseB45.cs y M₁ := by
    rw [← cs_commutator, F.perfect₁]
  have hPN : CaseB45.cs y M₁ ≤ c.Ninf := by
    intro p hp
    rw [mem_cs] at hp
    have := prOf_conj_mem c.N hy (F.M₁_le hp)
    simpa [mul_assoc] using this
  have hPC : ∀ p ∈ CaseB45.cs y M₁, ∀ f ∈ c.W ⊓ M₂, p * f = f * p := by
    intro p hp f hf
    rw [mem_cs] at hp
    have hf' : y⁻¹ * f * y ∈ c.W ⊓ M₂ := by
      have : f ∈ CaseB45.cs y (c.W ⊓ M₂) := by rw [hF₂]; exact hf
      rwa [mem_cs] at this
    have h := mem_centralizer_iff.mp (F.W₂_cent hf') _ hp
    calc p * f = y * ((y⁻¹ * p * y) * (y⁻¹ * f * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * f * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [h]
      _ = f * p := by group
  have := F.perf_le_M₁ hZ hperf hPN hPC
  exact this (mem_cs_iff.mpr hm)

end Fac

end CFSG.OddStandard.Seitz77
