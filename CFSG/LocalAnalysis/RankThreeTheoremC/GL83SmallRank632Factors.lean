module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

namespace SimpleFactorData

variable {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} {r : ℕ} {S : Fin r → Subgroup Y}

private lemma mem_map_conj {H : Subgroup Y} {y x : Y} :
    x ∈ H.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * x * y ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private lemma eq_of_le_of_conj_mem {T H : Subgroup Y} [IsSimpleGroup T] (hle : H ≤ T)
    (hH : ∀ t ∈ T, ∀ a ∈ H, t * a * t⁻¹ ∈ H) (hne : H ≠ ⊥) : H = T := by
  have hn : (H.subgroupOf T).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hH g g.2 a ha⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf T) with h1 | h1
  · exact absurd ((Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le hle) hne
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 h1)

private lemma mul_comm_of_inf_eq_bot {A B : Subgroup Y} (hAB : A ⊓ B = ⊥)
    (hA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    {a b : Y} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h1 : a * (b * a⁻¹ * b⁻¹) ∈ A := mul_mem ha (hA b hb a⁻¹ (inv_mem ha))
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B := mul_mem (hB a ha b hb) (inv_mem hb)
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨by simpa only [mul_assoc] using h1, h2⟩
  rw [hAB, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

private lemma conj_mem (h : SimpleFactorData N S) (i : Fin r) {n a : Y} (hn : n ∈ N)
    (ha : a ∈ S i) : n * a * n⁻¹ ∈ S i := by
  have := (h.normal i).conj_mem ⟨a, h.le i ha⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨n, hn⟩
  rwa [Subgroup.mem_subgroupOf] at this

private lemma apply_mulSingle {e : ((i : Fin r) → S i) ≃* N}
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : Y) = x i)
    (i : Fin r) (a : S i) : (e (Pi.mulSingle i a) : Y) = a := by
  rw [he i (Pi.mulSingle i a) fun j hj => Pi.mulSingle_eq_of_ne (M := fun l => S l) hj a,
    Pi.mulSingle_eq_same]

theorem inf_eq_bot (h : SimpleFactorData N S) {i j : Fin r} (hij : i ≠ j) : S i ⊓ S j = ⊥ := by
  obtain ⟨e, he⟩ := h.prod
  refine eq_bot_iff.2 fun a ha => ?_
  have ha' := Subgroup.mem_inf.1 ha
  have h1 : e (Pi.mulSingle i ⟨a, ha'.1⟩) = e (Pi.mulSingle j ⟨a, ha'.2⟩) :=
    Subtype.ext (by rw [apply_mulSingle he, apply_mulSingle he])
  have h2 := congrFun (e.injective h1) i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at h2
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)

theorem commute (h : SimpleFactorData N S) {i j : Fin r} (hij : i ≠ j) {a b : Y} (ha : a ∈ S i)
    (hb : b ∈ S j) : a * b = b * a :=
  mul_comm_of_inf_eq_bot (h.inf_eq_bot hij) (fun _ hb' _ ha' => h.conj_mem i (h.le j hb') ha')
    (fun _ ha' _ hb' => h.conj_mem j (h.le i ha') hb') ha hb

private lemma eq_one_of_forall_mul_comm (h : SimpleFactorData N S) (i : Fin r) {a : S i}
    (ha : ∀ b : S i, b * a = a * b) : a = 1 := by
  have := h.simple i
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (S i)) with h1 | h1
  · have h2 : a ∈ center (S i) := Subgroup.mem_center_iff.2 ha
    rwa [h1, Subgroup.mem_bot] at h2
  · exfalso
    obtain ⟨b, c, hbc⟩ := h.nonabelian i
    have h2 : c ∈ center (S i) := h1 ▸ Subgroup.mem_top c
    exact hbc (Subgroup.mem_center_iff.1 h2 b)

private lemma eq_one_of_mul_comm (h : SimpleFactorData N S) {k : Y} (hk : k ∈ N)
    (hc : ∀ j, ∀ b ∈ S j, k * b = b * k) : k = 1 := by
  obtain ⟨e, he⟩ := h.prod
  obtain ⟨x, hx⟩ := e.surjective ⟨k, hk⟩
  have hx' : x = 1 := funext fun j => h.eq_one_of_forall_mul_comm j fun b => by
    have h1 : e (Pi.mulSingle j b * x) = e (x * Pi.mulSingle j b) := Subtype.ext (by
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, apply_mulSingle he]
      exact (hc j b b.2).symm)
    simpa using congrFun (e.injective h1) j
  rw [hx', map_one] at hx
  exact (congrArg Subtype.val hx).symm

theorem exists_conj_eq (h : SimpleFactorData N S) [N.Normal] (y : Y) (i : Fin r) :
    ∃ j, (S i).map (MulAut.conj y).toMonoidHom = S j := by
  have := h.simple i
  have hmem : ∀ x, x ∈ (S i).map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * x * y ∈ S i :=
    fun x => mem_map_conj
  have hKs : IsSimpleGroup ((S i).map (MulAut.conj y).toMonoidHom) :=
    ((S i).equivMapOfInjective _ (MulAut.conj y).injective).symm.isSimpleGroup
  generalize (S i).map (MulAut.conj y).toMonoidHom = K at hmem hKs ⊢
  have hKN : ∀ x ∈ K, x ∈ N := fun x hx => by
    have h1 := ‹N.Normal›.conj_mem _ (h.le i ((hmem x).1 hx)) y
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h1
  have hKc : ∀ n ∈ N, ∀ a ∈ K, n * a * n⁻¹ ∈ K := fun n hn a ha => by
    rw [hmem] at ha ⊢
    have h1 := h.conj_mem i (‹N.Normal›.conj_mem n hn y⁻¹) ha
    convert h1 using 1
    group
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨j, hj⟩ : ∃ j, K ⊓ S j ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    refine hKne (eq_bot_iff.2 fun k hk => Subgroup.mem_bot.2 ?_)
    refine h.eq_one_of_mul_comm (hKN k hk) fun j b hb => ?_
    exact mul_comm_of_inf_eq_bot (hcon j) (fun b' hb' a ha => hKc b' (h.le j hb') a ha)
      (fun a ha b' hb' => h.conj_mem j (hKN a ha) hb') hk hb
  have := h.simple j
  have hjK : S j ≤ K := by
    have h1 : K ⊓ S j = S j := eq_of_le_of_conj_mem inf_le_right (fun t ht a ha =>
      Subgroup.mem_inf.2 ⟨hKc t (h.le j ht) a (Subgroup.mem_inf.1 ha).1,
        h.conj_mem j (h.le j ht) (Subgroup.mem_inf.1 ha).2⟩) hj
    exact h1.ge.trans inf_le_left
  have hSne : S j ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot (S j)).1 inferInstance
  exact ⟨j, (eq_of_le_of_conj_mem hjK (fun t ht a ha => h.conj_mem j (hKN t ht) ha) hSne).symm⟩

theorem normal_iInf_normalizer (h : SimpleFactorData N S) [N.Normal] :
    (⨅ i, normalizer ((S i : Subgroup Y) : Set Y)).Normal := by
  refine ⟨fun n hn g => Subgroup.mem_iInf.2 fun j => ?_⟩
  obtain ⟨k, hk⟩ := h.exists_conj_eq g⁻¹ j
  have hjk : ∀ x, x ∈ S j ↔ g⁻¹ * x * g ∈ S k := fun x => by
    rw [← hk, mem_map_conj, inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
  have hnk := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_iInf.1 hn k)
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  rw [hjk x, hjk (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹),
    show g⁻¹ * (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * x * g) * n⁻¹ by group]
  exact hnk _

theorem exists_diagonal (h : SimpleFactorData N S) [N.Normal] {i : Fin r} {y : Y} (hy : y ^ 3 = 1)
    (hmove : (S i).map (MulAut.conj y).toMonoidHom ≠ S i) :
    ∃ δ : ↥(S i) →* Y, Function.Injective δ ∧ (∀ s, δ s ∈ N) ∧ ∀ s, y * δ s = δ s * y := by
  obtain ⟨j, hj⟩ := h.exists_conj_eq y i
  obtain ⟨k, hk⟩ := h.exists_conj_eq y j
  obtain ⟨c, hc⟩ : ∃ c : Y →* Y, c = (MulAut.conj y).toMonoidHom := ⟨_, rfl⟩
  rw [← hc] at hj hk hmove
  have hc_apply : ∀ x, c x = y * x * y⁻¹ := fun x => by rw [hc]; rfl
  have hcinj : Function.Injective c := hc ▸ (MulAut.conj y).injective
  have hc3 : ∀ x, c (c (c x)) = x := fun x => by
    rw [hc_apply, hc_apply, hc_apply]
    calc y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = y * (y * y) * x * (y * (y * y))⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = x := by rw [← pow_three, hy, one_mul, inv_one, mul_one]
  have hmap3 : ∀ H : Subgroup Y, ((H.map c).map c).map c = H := fun H => by
    rw [Subgroup.map_map, Subgroup.map_map]
    convert Subgroup.map_id H
    exact MonoidHom.ext fun x => hc3 x
  have hci : ∀ s ∈ S i, c s ∈ S j := fun s hs => hj ▸ Subgroup.mem_map_of_mem c hs
  have hcj : ∀ s ∈ S j, c s ∈ S k := fun s hs => hk ▸ Subgroup.mem_map_of_mem c hs
  have hij : i ≠ j := by
    rintro rfl
    exact hmove hj
  have hjk : j ≠ k := by
    rintro rfl
    apply hmove
    apply Subgroup.map_injective hcinj
    rw [hj]
    exact hk
  have hik : i ≠ k := by
    rintro rfl
    apply hmove
    have h1 : ((S i).map c).map c = S i := by
      rw [hj]
      exact hk
    have h2 := congrArg (Subgroup.map c) h1
    rw [hmap3] at h2
    exact h2.symm
  let δ : ↥(S i) →* Y :=
    { toFun := fun s => (s : Y) * c s * c (c s)
      map_one' := by simp
      map_mul' := fun s t => by
        have h1 : (t : Y) * c s = c s * t := h.commute hij t.2 (hci s s.2)
        have h2 : (t : Y) * c (c s) = c (c s) * t := h.commute hik t.2 (hcj _ (hci s s.2))
        have h3 : c t * c (c s) = c (c s) * c t :=
          h.commute hjk (hci t t.2) (hcj _ (hci s s.2))
        simp only [Subgroup.coe_mul, map_mul]
        calc (s : Y) * t * (c s * c t) * (c (c s) * c (c t))
            = s * (t * c s) * c t * c (c s) * c (c t) := by simp only [mul_assoc]
          _ = s * (c s * t) * c t * c (c s) * c (c t) := by rw [h1]
          _ = s * c s * t * (c t * c (c s)) * c (c t) := by simp only [mul_assoc]
          _ = s * c s * t * (c (c s) * c t) * c (c t) := by rw [h3]
          _ = s * c s * (t * c (c s)) * c t * c (c t) := by simp only [mul_assoc]
          _ = s * c s * (c (c s) * t) * c t * c (c t) := by rw [h2]
          _ = s * c s * c (c s) * (t * c t * c (c t)) := by simp only [mul_assoc] }
  refine ⟨δ, ?_, fun s => ?_, fun s => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro s hs
    obtain ⟨e, he⟩ := h.prod
    have h1 : e (Pi.mulSingle i s * Pi.mulSingle j ⟨c s, hci s s.2⟩ *
        Pi.mulSingle k ⟨c (c s), hcj _ (hci s s.2)⟩) = 1 := by
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, apply_mulSingle he,
        apply_mulSingle he, apply_mulSingle he]
      exact hs
    have h2 := congrFun (e.injective (h1.trans (map_one e).symm)) i
    simpa [Pi.mulSingle_eq_of_ne hij, Pi.mulSingle_eq_of_ne hik] using h2
  · exact mul_mem (mul_mem (h.le i s.2) (h.le j (hci s s.2))) (h.le k (hcj _ (hci s s.2)))
  · have hsj : Commute (c s) (s : Y) := (h.commute hij s.2 (hci s s.2)).symm
    have hsk : Commute (c (c s)) (s : Y) := (h.commute hik s.2 (hcj _ (hci s s.2))).symm
    have h1 : c (δ s) = δ s := by
      change c ((s : Y) * c s * c (c s)) = s * c s * c (c s)
      rw [map_mul, map_mul, hc3]
      exact (hsj.mul_left hsk).eq.trans (mul_assoc _ _ _).symm
    rw [hc_apply] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1

end SimpleFactorData

end CFSG.LocalAnalysis.RankThreeTheoremC
