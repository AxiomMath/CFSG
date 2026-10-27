module

public import CFSG.Fischer.Classification.Basic.Trichotomy
public import TauCeti.GroupTheory.DerivedCentralQuotient

public section

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace CFSG.Fischer.Classification

open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

private def sixo_B (a : X) (N : Subgroup X) : Set X := {e | e ∈ E ∧ a⁻¹ * e ∈ N}

private theorem sixo_mem_of_mem_of_inv_mem {N : Subgroup X} {a b c : X}
    (hac : a⁻¹ * c ∈ N) (hbc : b⁻¹ * c ∈ N) : a⁻¹ * b ∈ N := by
  have h : a⁻¹ * b = (a⁻¹ * c) * (b⁻¹ * c)⁻¹ := by group
  rw [h]
  exact N.mul_mem hac (N.inv_mem hbc)

private theorem sixo_coset_not_mem_of_mul_mem {N : Subgroup X} {a x y : X}
    (hx : a⁻¹ * x ∉ N) (hxy : x⁻¹ * y ∈ N) : a⁻¹ * y ∉ N := by
  intro hy
  apply hx
  have h : a⁻¹ * x = (a⁻¹ * y) * (x⁻¹ * y)⁻¹ := by group
  rw [h]
  exact N.mul_mem hy (N.inv_mem hxy)

theorem Pair.inv_mul_mem_of_commute (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) (hab : a * b = b * a) : a⁻¹ * b ∈ N := by
  have := hN
  by_contra hne
  refine hNZ (Pair.normal_le_center_of_commute hP hN hNs ha hb hab fun n hn => ?_)
  by_contra hc
  apply hne
  have hb' := Pair.conj_mem hP hb n
  have h1 := Pair.mul_conj_left_eq hP ha hb' hc
  have hπ : (QuotientGroup.mk (n * b * n⁻¹) : X ⧸ N) = QuotientGroup.mk b := by
    rw [QuotientGroup.eq]
    have := N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) b⁻¹)
    convert this using 1
    group
  generalize n * b * n⁻¹ = b' at h1 hπ
  have key : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
    rw [← hπ]
    conv_lhs => rw [← h1]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hπ]
    have hab' : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
      rw [← QuotientGroup.mk_mul, hab, QuotientGroup.mk_mul]
    calc (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b * QuotientGroup.mk a *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹
        = QuotientGroup.mk a * (QuotientGroup.mk b * QuotientGroup.mk a) *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹ := by group
      _ = QuotientGroup.mk a := by rw [← hab']; group
  exact QuotientGroup.eq.1 key.symm

private theorem sixo_B_conj_mem (hP : Pair X E) {N : Subgroup X} (hN : N.Normal) {a e : X}
    (he : e ∈ sixo_B (E := E) a N) (n : X) (hn : n ∈ N) :
    n * e * n⁻¹ ∈ sixo_B (E := E) a N := by
  refine ⟨Pair.conj_mem hP he.1 n, ?_⟩
  have h1 : a⁻¹ * n * a ∈ N := by
    have h := hN.conj_mem n hn a⁻¹
    rwa [inv_inv] at h
  have hid : a⁻¹ * (n * e * n⁻¹) = (a⁻¹ * n * a) * (a⁻¹ * e) * n⁻¹ := by group
  rw [hid]
  exact N.mul_mem (N.mul_mem h1 he.2) (N.inv_mem hn)

private theorem sixo_B_mul_conj_mem (hP : Pair X E) {N : Subgroup X} (hN : N.Normal) {a e y : X}
    (he : e ∈ sixo_B (E := E) a N) (hy : y ∈ sixo_B (E := E) a N) :
    e * y * e⁻¹ ∈ sixo_B (E := E) a N := by
  refine ⟨Pair.conj_mem hP hy.1 e, ?_⟩
  have h1 : a * (a⁻¹ * y) * a⁻¹ ∈ N := hN.conj_mem _ hy.2 a
  have h2 : a * (a⁻¹ * e)⁻¹ * a⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem he.2) a
  have hid : a⁻¹ * (e * y * e⁻¹) =
      (a⁻¹ * e) * (a * (a⁻¹ * y) * a⁻¹) * (a * (a⁻¹ * e)⁻¹ * a⁻¹) := by group
  rw [hid]
  exact N.mul_mem (N.mul_mem he.2 h1) h2

private theorem sixo_mul_comm_mem (hP : Pair X E) {N : Subgroup X} {a c : X}
    (ha : a ∈ E) (hc : c ∈ E) (hacN : a⁻¹ * c ∈ N) : c * a ∈ N := by
  have hac : a * c ∈ N := by
    have h := hacN
    rwa [Pair.inv_eq hP ha] at h
  have h := N.inv_mem hac
  rwa [mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hc] at h

private theorem sixo_conj_mul_conj_mem (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    {a b c : X} (ha : a ∈ E) (hb : b ∈ E) (hacN : a⁻¹ * c ∈ N) : b * (a * c) * b ∈ N := by
  have hac : a * c ∈ N := by
    have h := hacN
    rwa [Pair.inv_eq hP ha] at h
  have h := hN.conj_mem (a * c) hac b
  rwa [Pair.inv_eq hP hb] at h

private theorem sixo_bab_not_mem (hP : Pair X E) {N : Subgroup X} {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) (hab : a * b ≠ b * a) (hbN : a⁻¹ * b ∉ N) :
    a⁻¹ * (b * a * b) ∉ N := by
  intro h
  have h' : a * (b * a * b) ∈ N := by
    have hh := h
    rwa [Pair.inv_eq hP ha] at hh
  have hba : b * a ∈ N := by
    have hid : a * (b * a * b) = b * a := by
      rw [← Pair.mul_mul_eq hP ha hb hab]
      calc a * (a * b * a) = (a * a) * (b * a) := by group
        _ = b * a := by rw [Pair.mul_self hP ha, one_mul]
    rwa [hid] at h'
  have hab' : a * b = (b * a)⁻¹ := by
    rw [mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hb]
  have habN : a * b ∈ N := by
    rw [hab']
    exact N.inv_mem hba
  apply hbN
  rwa [Pair.inv_eq hP ha]

private theorem sixo_not_commute_of_coset_ne (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a e f : X}
    (he : e ∈ E) (hf : f ∈ E) (heN : a⁻¹ * e ∈ N) (hfN : a⁻¹ * f ∉ N) :
    e * f ≠ f * e := by
  intro h
  apply hfN
  have hef : e⁻¹ * f ∈ N := Pair.inv_mul_mem_of_commute hP hN hNs hNZ he hf h
  have hid : a⁻¹ * f = (a⁻¹ * e) * (e⁻¹ * f) := by group
  rw [hid]
  exact N.mul_mem heN hef

private theorem sixo_N_le_closure (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a : X} (ha : a ∈ E) :
    N ≤ Subgroup.closure (sixo_B (E := E) a N) := by
  have haB : a ∈ sixo_B (E := E) a N := ⟨ha, by rw [inv_mul_cancel]; exact N.one_mem⟩
  have hconjK : ∀ g : X,
      (∀ e ∈ sixo_B (E := E) a N, g * e * g⁻¹ ∈ sixo_B (E := E) a N) →
      ∀ k ∈ Subgroup.closure (sixo_B (E := E) a N),
        g * k * g⁻¹ ∈ Subgroup.closure (sixo_B (E := E) a N) := by
    intro g hg k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hg x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ hx
  have hpres : ∀ n ∈ N, ∀ k ∈ Subgroup.closure (sixo_B (E := E) a N),
      n * k * n⁻¹ ∈ Subgroup.closure (sixo_B (E := E) a N) :=
    fun n hn => hconjK n fun e he => sixo_B_conj_mem hP hN he n hn
  have hpres_inv : ∀ n ∈ N, ∀ k ∈ Subgroup.closure (sixo_B (E := E) a N),
      n⁻¹ * k * n ∈ Subgroup.closure (sixo_B (E := E) a N) := by
    intro n hn
    simpa only [inv_inv] using
      hconjK n⁻¹ fun e he => sixo_B_conj_mem hP hN he n⁻¹ (N.inv_mem hn)
  have hKn : ((Subgroup.closure (sixo_B (E := E) a N) ⊓ N).subgroupOf N).Normal := by
    refine ⟨fun x hx n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hpres n n.2 x hx.1
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hN.conj_mem x hx.2 n
  have := hKn
  rcases hNs.eq_bot_or_eq_top_of_normal
    ((Subgroup.closure (sixo_B (E := E) a N) ⊓ N).subgroupOf N) with hbot | htop
  · exfalso
    apply hNZ
    have h1 : ∀ n ∈ N, a * (n * a * n⁻¹) = 1 := by
      intro n hn
      have hnaB : n * a * n⁻¹ ∈ sixo_B (E := E) a N := sixo_B_conj_mem hP hN haB n hn
      have hmemK : a * (n * a * n⁻¹) ∈ Subgroup.closure (sixo_B (E := E) a N) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure haB) (Subgroup.subset_closure hnaB)
      have hmemN : a * (n * a * n⁻¹) ∈ N := by
        have h := hnaB.2
        rwa [Pair.inv_eq hP ha] at h
      have hmem : (⟨a * (n * a * n⁻¹), hmemN⟩ : N) ∈
          (Subgroup.closure (sixo_B (E := E) a N) ⊓ N).subgroupOf N :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hmemK, hmemN⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      simpa using congrArg Subtype.val hmem
    refine Pair.normal_le_center_of_commute hP hN hNs ha ha rfl fun n hn => ?_
    have hn' : n * a * n⁻¹ = a := by
      have h := h1 n hn
      rw [← Pair.mul_self hP ha] at h
      exact mul_left_cancel h
    rw [h1 n hn, hn', Pair.mul_self hP ha]
  · intro n hn
    have hmem : (⟨n, hn⟩ : N) ∈
        (Subgroup.closure (sixo_B (E := E) a N) ⊓ N).subgroupOf N := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 hmem).1

private theorem sixo_conj_mem_of_mem (hP : Pair X E) {N : Subgroup X} (hN : N.Normal) {a : X}
    {Z : Set X} (hZsub : Z ⊆ sixo_B (E := E) a N)
    (hcl : ∀ y ∈ Z, ∀ z ∈ sixo_B (E := E) a N, y * z ≠ z * y → z ∈ Z)
    {e : X} (he : e ∈ sixo_B (E := E) a N) {y : X} (hy : y ∈ Z) :
    e * y * e⁻¹ ∈ Z := by
  by_cases hec : e * y = y * e
  · have heq : e * y * e⁻¹ = y := by rw [hec, mul_assoc, mul_inv_cancel, mul_one]
    rwa [heq]
  · have hyB : y ∈ sixo_B (E := E) a N := hZsub hy
    have hweB : y * e * y ∈ sixo_B (E := E) a N := by
      have h := sixo_B_mul_conj_mem hP hN hyB he
      rwa [Pair.inv_eq hP hyB.1] at h
    have hne : y * (y * e * y) ≠ (y * e * y) * y := by
      intro h
      apply hec
      calc e * y = (y * y) * (e * y) := by rw [Pair.mul_self hP hyB.1, one_mul]
        _ = y * (y * e * y) := by group
        _ = (y * e * y) * y := h
        _ = y * e * (y * y) := by group
        _ = y * e := by rw [Pair.mul_self hP hyB.1, mul_one]
    have hmem := hcl y hy (y * e * y) hweB hne
    have heq : e * y * e⁻¹ = y * e * y := by
      rw [Pair.inv_eq hP he.1, ← Pair.mul_mul_eq hP hyB.1 he.1 (fun h => hec h.symm)]
    rwa [heq]

private theorem sixo_connected (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a : X} (ha : a ∈ E)
    {Z : Set X} (hZsub : Z ⊆ sixo_B (E := E) a N) (haZ : a ∈ Z)
    (hcl : ∀ y ∈ Z, ∀ z ∈ sixo_B (E := E) a N, y * z ≠ z * y → z ∈ Z) :
    ∀ x ∈ sixo_B (E := E) a N, x ∈ Z := by
  have hBZfwd : ∀ e ∈ sixo_B (E := E) a N, ∀ y : X, y ∈ Z → e * y * e⁻¹ ∈ Z :=
    fun e he y hy => sixo_conj_mem_of_mem hP hN hZsub hcl he hy
  let H : Subgroup X :=
    { carrier := {k | ∀ y : X, y ∈ Z ↔ k * y * k⁻¹ ∈ Z}
      one_mem' := fun y => by simp
      mul_mem' := fun {k l} hk hl y => by
        rw [show k * l * y * (k * l)⁻¹ = k * (l * y * l⁻¹) * k⁻¹ by group]
        exact (hl y).trans (hk _)
      inv_mem' := fun {k} hk y => by
        have h := hk (k⁻¹ * y * k)
        rw [show k * (k⁻¹ * y * k) * k⁻¹ = y by group] at h
        simpa using h.symm }
  have hBH : sixo_B (E := E) a N ⊆ (H : Set X) := by
    intro e he
    show ∀ y : X, y ∈ Z ↔ e * y * e⁻¹ ∈ Z
    intro y
    exact ⟨hBZfwd e he y, fun hy => by
      have h := hBZfwd e he (e * y * e⁻¹) hy
      have hid : e * (e * y * e⁻¹) * e⁻¹ = y := by
        rw [Pair.inv_eq hP he.1]
        calc e * (e * y * e) * e = (e * e) * y * (e * e) := by group
          _ = y := by rw [Pair.mul_self hP he.1]; group
      rwa [hid] at h⟩
  have hKH : Subgroup.closure (sixo_B (E := E) a N) ≤ H :=
    (Subgroup.closure_le H).2 fun e he => hBH he
  have hNK : N ≤ Subgroup.closure (sixo_B (E := E) a N) := sixo_N_le_closure hP hN hNs hNZ ha
  intro x hxB
  by_contra hxZ
  have hnex : ∃ n ∈ N, a * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * a := by
    by_contra hcon
    have h : ∀ n ∈ N, a * (n * x * n⁻¹) = (n * x * n⁻¹) * a := by
      intro n hn
      by_contra hne
      exact hcon ⟨n, hn, hne⟩
    have hax : a * x = x * a := by
      have h1 := h 1 N.one_mem
      simpa using h1
    exact hNZ (Pair.normal_le_center_of_commute hP hN hNs ha hxB.1 hax h)
  obtain ⟨n, hn, hna⟩ := hnex
  have hnxB : n * x * n⁻¹ ∈ sixo_B (E := E) a N := sixo_B_conj_mem hP hN hxB n hn
  have hnxZ : n * x * n⁻¹ ∈ Z := hcl a haZ _ hnxB hna
  have hnH : n ∈ H := hKH (hNK hn)
  have hconj : n⁻¹ * (n * x * n⁻¹) * n ∈ Z := by
    have h := (H.inv_mem hnH) (n * x * n⁻¹)
    simpa using h.1 hnxZ
  have hx' : x ∈ Z := by
    have h := hconj
    rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h
  exact hxZ hx'

private theorem sixo_radius_two (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a c : X} (ha : a ∈ E)
    (hc : c ∈ sixo_B (E := E) a N) (hac : a ≠ c) (hcomm : a * c = c * a) :
    ∃ t ∈ sixo_B (E := E) a N, a * t ≠ t * a ∧ t * c ≠ c * t := by
  have haB : a ∈ sixo_B (E := E) a N := ⟨ha, by rw [inv_mul_cancel]; exact N.one_mem⟩
  let Z : Set X := {y | y ∈ sixo_B (E := E) a N ∧ (y = a ∨ y * a ≠ a * y ∨
    ∃ t ∈ sixo_B (E := E) a N, a * t ≠ t * a ∧ t * y ≠ y * t)}
  have hZsub : Z ⊆ sixo_B (E := E) a N := fun _ hy => hy.1
  have haZ : a ∈ Z := ⟨haB, Or.inl rfl⟩
  have hcl : ∀ y ∈ Z, ∀ z ∈ sixo_B (E := E) a N, y * z ≠ z * y → z ∈ Z := by
    rintro y ⟨hyB, hy | hya | ⟨t, htB, hat, hty⟩⟩ z hzB hyz
    · exact ⟨hzB, Or.inr (Or.inl (by rw [hy] at hyz; exact fun h => hyz h.symm))⟩
    · exact ⟨hzB, Or.inr (Or.inr ⟨y, hyB, fun h => hya h.symm, hyz⟩)⟩
    · by_cases hya' : y * a = a * y
      · by_cases htz : t * z = z * t
        · have hyt : y * t ≠ t * y := fun h => hty h.symm
          have hwB : y * t * y ∈ sixo_B (E := E) a N := by
            have h := sixo_B_mul_conj_mem hP hN hyB htB
            rwa [Pair.inv_eq hP hyB.1] at h
          have haw : a * (y * t * y) ≠ (y * t * y) * a := by
            intro h
            apply hat
            have hy' : Commute a y := hya'.symm
            have hw' : Commute a (y * t * y) := h
            have h2 := (Commute.mul_right (Commute.inv_right hy') hw').mul_right hy'
            have hid : y⁻¹ * (y * t * y) * y = t := by
              rw [Pair.inv_eq hP hyB.1]
              calc y * (y * t * y) * y = (y * y) * t * (y * y) := by group
                _ = t := by rw [Pair.mul_self hP hyB.1]; group
            rw [hid] at h2
            exact h2.eq
          have hwz : (y * t * y) * z ≠ z * (y * t * y) := by
            intro h
            apply hyz
            have h2 := (Commute.mul_left (Commute.mul_left htz h) (Commute.inv_left htz))
            have hid : t * (y * t * y) * t⁻¹ = y := by
              rw [Pair.mul_mul_eq hP hyB.1 htB.1 hyt, Pair.inv_eq hP htB.1]
              calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
                _ = y := by rw [Pair.mul_self hP htB.1]; group
            rw [hid] at h2
            exact h2.eq
          exact ⟨hzB, Or.inr (Or.inr ⟨y * t * y, hwB, haw, hwz⟩)⟩
        · exact ⟨hzB, Or.inr (Or.inr ⟨t, htB, hat, htz⟩)⟩
      · exact ⟨hzB, Or.inr (Or.inr ⟨y, hyB, fun h => hya' h.symm, hyz⟩)⟩
  have hcZ : c ∈ Z := sixo_connected hP hN hNs hNZ ha hZsub haZ hcl c hc
  rcases hcZ with ⟨-, hca | hcz | ⟨t, htB, hat, htc⟩⟩
  · exact absurd hca.symm hac
  · exact absurd hcomm.symm hcz
  · exact ⟨t, htB, hat, htc⟩

theorem Pair.exists_not_commute_of_inv_mul_mem (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a c : X} (ha : a ∈ E)
    (hc : c ∈ E) (hac : a ≠ c) (hcomm : a * c = c * a) (hacN : a⁻¹ * c ∈ N) :
    ∃ t ∈ E, a⁻¹ * t ∈ N ∧ t * a ≠ a * t ∧ t * c ≠ c * t := by
  have hcB : c ∈ sixo_B (E := E) a N := ⟨hc, hacN⟩
  obtain ⟨t, htB, hta, htc⟩ := sixo_radius_two hP hN hNs hNZ ha hcB hac hcomm
  exact ⟨t, htB.1, htB.2, fun h => hta h.symm, htc⟩

private theorem sixo_coset_ne (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hNZ : ¬ N ≤ Subgroup.center X) {a c b t : X} (ha : a ∈ E)
    (hc : c ∈ E) (hb : b ∈ E) (ht : t ∈ E) (hacN : a⁻¹ * c ∈ N) (hatN : a⁻¹ * t ∈ N)
    (hbN : a⁻¹ * b ∉ N) (hab : a * b ≠ b * a) :
    t * b ≠ b * t ∧ t * (b * a * b) ≠ b * a * b * t ∧
      t * (b * c * b) ≠ b * c * b * t ∧
        t * (a * c * b * c * a) ≠ a * c * b * c * a * t := by
  have hbabN : a⁻¹ * (b * a * b) ∉ N := sixo_bab_not_mem hP ha hb hab hbN
  have hbcbN : a⁻¹ * (b * c * b) ∉ N := by
    refine sixo_coset_not_mem_of_mul_mem hbabN ?_
    have hid : (b * a * b)⁻¹ * (b * c * b) = b * (a * c) * b := by
      rw [mul_inv_rev, mul_inv_rev, Pair.inv_eq hP hb, Pair.inv_eq hP ha]
      calc b * (a * b) * (b * c * b) = b * a * (b * b) * c * b := by group
        _ = b * (a * c) * b := by rw [Pair.mul_self hP hb]; group
    rw [hid]
    exact sixo_conj_mul_conj_mem hP hN ha hb hacN
  have hacbcaE : a * c * b * c * a ∈ E := by
    have h := Pair.conj_mem hP hb (a * c)
    rw [mul_inv_rev, Pair.inv_eq hP ha, Pair.inv_eq hP hc] at h
    simpa only [mul_assoc] using h
  have hacbcaN : a⁻¹ * (a * c * b * c * a) ∉ N := by
    refine sixo_coset_not_mem_of_mul_mem hbN ?_
    have hid : b⁻¹ * (a * c * b * c * a) = (b * (a * c) * b) * (c * a) := by
      rw [Pair.inv_eq hP hb]
      group
    rw [hid]
    exact N.mul_mem (sixo_conj_mul_conj_mem hP hN ha hb hacN)
      (sixo_mul_comm_mem hP ha hc hacN)
  exact ⟨sixo_not_commute_of_coset_ne hP hN hNs hNZ ht hb hatN hbN,
    sixo_not_commute_of_coset_ne hP hN hNs hNZ ht (Pair.mul_mul_mem hP hb ha) hatN hbabN,
    sixo_not_commute_of_coset_ne hP hN hNs hNZ ht (Pair.mul_mul_mem hP hb hc) hatN hbcbN,
    sixo_not_commute_of_coset_ne hP hN hNs hNZ ht hacbcaE hatN hacbcaN⟩

private theorem sixo_commutator_le (hP : Pair X E) {N : Subgroup X} (hN : N.Normal) {a : X}
    (hall : ∀ e ∈ E, a⁻¹ * e ∈ N) : commutator X ≤ N := by
  have := hN
  refine Pair.commutator_le_of_forall hP fun e he f hf => ?_
  have hnf : a⁻¹ * f ∈ N := hall f hf
  have hne : a⁻¹ * e ∈ N := hall e he
  have h1 : a⁻¹ * f * (a⁻¹ * e)⁻¹ ∈ N := N.mul_mem hnf (N.inv_mem hne)
  have h2 : a * (a⁻¹ * f * (a⁻¹ * e)⁻¹) * a⁻¹ ∈ N := hN.conj_mem _ h1 a
  have hid : f * e⁻¹ = a * (a⁻¹ * f * (a⁻¹ * e)⁻¹) * a⁻¹ := by group
  rw [hid]
  exact h2

theorem Pair.isSimpleGroup_commutator_of_six (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥)
    (hsix : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ s ∈ E, a ≠ c → a * c = c * a → a * b ≠ b * a →
      b * c ≠ c * b → s * a ≠ a * s → s * b ≠ b * s → s * c ≠ c * s →
      s * (b * a * b) ≠ b * a * b * s → s * (b * c * b) ≠ b * c * b * s →
      s * (a * c * b * c * a) ≠ a * c * b * c * a * s → False) :
    IsSimpleGroup (commutator X) := by
  have := Pair.finite hP
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  have htop : (⊤ : Subgroup X) ≠ ⊥ := by
    intro h
    have hmem := Subgroup.mem_top e₀
    rw [h, Subgroup.mem_bot] at hmem
    exact Pair.ne_one hP he₀ hmem
  obtain ⟨N, hNn, -, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have := hNn
  have hNZ : ¬ N ≤ Subgroup.center X := fun h => hNbot (by rw [← le_bot_iff, ← hZ]; exact h)
  have hNle : N ≤ commutator X := by
    have : Group.IsPerfect ↥N := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative
      fun h => hNsol (Group.isSolvable_of_comm (isMulCommutative_iff.mp h))
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ commutator X := Subgroup.commutator_mono le_top le_top
  obtain ⟨a, ha, c, hc, hac, hcomm⟩ := Pair.exists_ne_commute_of_three hP hZ h3
  have hacN : a⁻¹ * c ∈ N := Pair.inv_mul_mem_of_commute hP hNn hNs hNZ ha hc hcomm
  have hall : ∀ e ∈ E, a⁻¹ * e ∈ N := by
    intro b hb
    by_contra hbN
    have hab : a * b ≠ b * a := fun h =>
      hbN (Pair.inv_mul_mem_of_commute hP hNn hNs hNZ ha hb h)
    have hbc : b * c ≠ c * b := fun h =>
      hbN (sixo_mem_of_mem_of_inv_mem hacN
        (Pair.inv_mul_mem_of_commute hP hNn hNs hNZ hb hc h))
    obtain ⟨t, ht, hatN, hta, htc⟩ :=
      Pair.exists_not_commute_of_inv_mul_mem hP hNn hNs hNZ ha hc hac hcomm hacN
    obtain ⟨htb, htab, htcb, htacbca⟩ :=
      sixo_coset_ne hP hNn hNs hNZ ha hc hb ht hacN hatN hbN hab
    exact hsix a ha b hb c hc t ht hac hcomm hab hbc hta htb htc htab htcb htacbca
  have hle : commutator X ≤ N := sixo_commutator_le hP hNn hall
  rw [le_antisymm hle hNle]
  exact hNs

end CFSG.Fischer.Classification
