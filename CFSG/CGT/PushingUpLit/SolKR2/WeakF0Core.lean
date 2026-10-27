module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakInner
import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

theorem card_sup_mul_card_inf_normal {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_normalizes {G : Type*} [Group G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem mul_mul_mul_mul_eq_pow_four {G : Type*} [Group G] (u : G) :
    u * u * (u * u) = u ^ 4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]

theorem isElemAbelian_two {G : Type*} [Group G] {E : Subgroup G}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    CFSG.Open.IsElemAbelian 2 E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, fun z hz => by rw [sq]; exact hsq z hz⟩

section Basic

variable {G : Type} [Group G]

abbrev dF0 (U : Subgroup G) (g x : G) : Subgroup G :=
  (dX U x ⊔ omegaOneSub (conjSubgroup g U)) ⊓ Subgroup.centralizer (dX U x : Set G)

theorem dF0_comm_dX {U : Subgroup G} {g x f z : G} (hf : f ∈ dF0 U g x) (hz : z ∈ dX U x) :
    f * z = z * f :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hf).2 z hz).symm

theorem dF0_le_normalizer {U : Subgroup G} {g x : G} {T : Subgroup G} (hT : T ≤ dX U x) :
    dF0 U g x ≤ Subgroup.normalizer (T : Set G) :=
  le_normalizer_of_comm fun _ hf _ ht => dF0_comm_dX hf (hT ht)

theorem inv_mul_mem_dF0 {U : Subgroup G} {g x a y : G}
    (ha : a ∈ omegaOneSub (conjSubgroup g U)) (hy : y ∈ dS U g x)
    (hay : ∀ z ∈ dX U x, a * z * a⁻¹ = y * z * y⁻¹) : y⁻¹ * a ∈ dF0 U g x := by
  have hyX : y ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hy)
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left ((dX U x).inv_mem hyX))
    (Subgroup.mem_sup_right ha), Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have h2 := hay w hw
  calc w * (y⁻¹ * a) = y⁻¹ * (y * w * y⁻¹) * a := by group
    _ = y⁻¹ * (a * w * a⁻¹) * a := by rw [h2]
    _ = (y⁻¹ * a) * w := by group

theorem exists_U0_ne_one {U : Subgroup G} {g α x : G} (D : Data31 U g α x) :
    ∃ β ∈ omegaOneSub U, β ≠ 1 := by
  obtain ⟨u, hu, hu2⟩ := D.core.exp_ne
  refine ⟨u * u, (mem_omegaOneSub_iff D.core.comm).mpr ⟨Subgroup.mul_mem _ hu hu, ?_⟩, ?_⟩
  · calc u * u * (u * u) = u ^ 4 := mul_mul_mul_mul_eq_pow_four u
      _ = 1 := D.core.exp u hu
  · intro h
    exact hu2 (by rw [sq]; exact h)

end Basic

section Certificates34

variable {G : Type} [Group G] [Finite G]

namespace Inner

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem mem_dF0 {f : G} (hf : f ∈ dF0 U g x) :
    ∃ a ∈ omegaOneSub (conjSubgroup g U), ∃ y ∈ dS U g x, f = y⁻¹ * a ∧
      ∀ z ∈ dX U x, a * z * a⁻¹ = y * z * y⁻¹ := by
  obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.mp hf
  obtain ⟨z, hz, a, ha, rfl⟩ := exists_mul_of_mem_sup (A0_le_normalizer_X D hCen hU) hf1
  obtain ⟨y, hyS, hy⟩ := inner_mem_S D hCen hU ha
  have hyX : y ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hyS)
  have hcf := Subgroup.mem_centralizer_iff.mp hf2
  have hzy : z * y = 1 := by
    refine center_X D hCen hU (Subgroup.mul_mem _ hz hyX) (fun w hw => ?_)
    have h1 := hcf w hw
    have h2 := hy w hw
    calc z * y * w = (z * y) * w * (z * y)⁻¹ * (z * y) := by group
      _ = z * (y * w * y⁻¹) * z⁻¹ * (z * y) := by group
      _ = z * (a * w * a⁻¹) * z⁻¹ * (z * y) := by rw [h2]
      _ = (z * a) * w * (z * a)⁻¹ * (z * y) := by group
      _ = w * (z * y) := by
        rw [show (z * a) * w * (z * a)⁻¹ = w by rw [← h1]; group]
  have hz' : z = y⁻¹ := eq_inv_of_mul_eq_one_left hzy
  exact ⟨a, ha, y, hyS, by rw [hz'], hy⟩

theorem exists_mul_S_dF0 {a : G} (ha : a ∈ omegaOneSub (conjSubgroup g U)) :
    ∃ s ∈ dS U g x, ∃ f ∈ dF0 U g x, a = s * f := by
  obtain ⟨y, hyS, hy⟩ := inner_mem_S D hCen hU ha
  exact ⟨y, hyS, y⁻¹ * a, inv_mul_mem_dF0 ha hyS hy, by group⟩

theorem exists_A0_of_dF0 {f : G} (hf : f ∈ dF0 U g x) :
    ∃ a ∈ omegaOneSub (conjSubgroup g U), ∃ s ∈ dS U g x, a = s * f := by
  obtain ⟨a, ha, y, hy, rfl, -⟩ := mem_dF0 D hCen hU hf
  exact ⟨a, ha, y, hy, by group⟩

theorem dF0_inf_dX : dF0 U g x ⊓ dX U x = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.mp hf
  rw [Subgroup.mem_bot]
  exact center_X D hCen hU hf2 fun w hw => dF0_comm_dX hf1 hw

theorem dS_inf_dF0 : dS U g x ⊓ dF0 U g x = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨hf1, hf2⟩ := Subgroup.mem_inf.mp hf
  have hmem : f ∈ dF0 U g x ⊓ dX U x :=
    Subgroup.mem_inf.mpr ⟨hf2, dS2_le_dX U x (dS_le_dS2 U g x hf1)⟩
  rwa [dF0_inf_dX D hCen hU] at hmem

theorem dF0_comm {f f' : G} (hf : f ∈ dF0 U g x) (hf' : f' ∈ dF0 U g x) : f * f' = f' * f := by
  obtain ⟨a, ha, y, hy, rfl, hay⟩ := mem_dF0 D hCen hU hf
  obtain ⟨a', ha', y', hy', rfl, hay'⟩ := mem_dF0 D hCen hU hf'
  have hy'X : y'⁻¹ ∈ dX U x := (dX U x).inv_mem (dS2_le_dX U x (dS_le_dS2 U g x hy'))
  have hyX : y⁻¹ ∈ dX U x := (dX U x).inv_mem (dS2_le_dX U x (dS_le_dS2 U g x hy))
  have h1 := hay _ hy'X
  have h2 := hay' _ hyX
  have hyy' : y * y' = y' * y := S_comm D hCen hU hy hy'
  have haa' : a * a' = a' * a :=
    D.core.comm_conj' g a (omegaOneSub_le _ ha) a' (omegaOneSub_le _ ha')
  have hinv : y'⁻¹ * y⁻¹ = y⁻¹ * y'⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hyy']
  have e1 : y⁻¹ * a * (y'⁻¹ * a') = y'⁻¹ * y⁻¹ * (a * a') := by
    calc y⁻¹ * a * (y'⁻¹ * a') = y⁻¹ * (a * y'⁻¹ * a⁻¹) * (a * a') := by group
      _ = y⁻¹ * (y * y'⁻¹ * y⁻¹) * (a * a') := by rw [h1]
      _ = y'⁻¹ * y⁻¹ * (a * a') := by group
  have e2 : y'⁻¹ * a' * (y⁻¹ * a) = y⁻¹ * y'⁻¹ * (a' * a) := by
    calc y'⁻¹ * a' * (y⁻¹ * a) = y'⁻¹ * (a' * y⁻¹ * a'⁻¹) * (a' * a) := by group
      _ = y'⁻¹ * (y' * y⁻¹ * y'⁻¹) * (a' * a) := by rw [h2]
      _ = y⁻¹ * y'⁻¹ * (a' * a) := by group
  rw [e1, e2, hinv, haa']

theorem dF0_sq {f : G} (hf : f ∈ dF0 U g x) : f * f = 1 := by
  obtain ⟨a, ha, y, hy, rfl, hay⟩ := mem_dF0 D hCen hU hf
  have hyX : y⁻¹ ∈ dX U x := (dX U x).inv_mem (dS2_le_dX U x (dS_le_dS2 U g x hy))
  have h1 := hay _ hyX
  have hy2 : y * y = 1 := S_sq D hCen hU hy
  have ha2 : a * a = 1 := D.core.sq_omega ha
  calc y⁻¹ * a * (y⁻¹ * a) = y⁻¹ * (a * y⁻¹ * a⁻¹) * (a * a) := by group
    _ = y⁻¹ * (y * y⁻¹ * y⁻¹) * (a * a) := by rw [h1]
    _ = (y * y)⁻¹ * (a * a) := by group
    _ = 1 := by simp [hy2, ha2]

theorem dE_comm {e e' : G} (he : e ∈ dS U g x ⊔ dF0 U g x) (he' : e' ∈ dS U g x ⊔ dF0 U g x) :
    e * e' = e' * e := by
  have hN : dF0 U g x ≤ Subgroup.normalizer (dS U g x : Set G) :=
    dF0_le_normalizer ((dS_le_dS2 U g x).trans (dS2_le_dX U x))
  obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_of_mem_sup hN he
  obtain ⟨s', hs', f', hf', rfl⟩ := exists_mul_of_mem_sup hN he'
  have hss' : s * s' = s' * s := S_comm D hCen hU hs hs'
  have hff' : f * f' = f' * f := dF0_comm D hCen hU hf hf'
  have hfs' : f * s' = s' * f := dF0_comm_dX hf (dS2_le_dX U x (dS_le_dS2 U g x hs'))
  have hf's : f' * s = s * f' := dF0_comm_dX hf' (dS2_le_dX U x (dS_le_dS2 U g x hs))
  calc s * f * (s' * f') = s * (f * s') * f' := by group
    _ = s * (s' * f) * f' := by rw [hfs']
    _ = (s * s') * (f * f') := by group
    _ = (s' * s) * (f' * f) := by rw [hss', hff']
    _ = s' * (s * f') * f := by group
    _ = s' * (f' * s) * f := by rw [hf's]
    _ = s' * f' * (s * f) := by group

theorem dE_sq {e : G} (he : e ∈ dS U g x ⊔ dF0 U g x) : e * e = 1 := by
  have hN : dF0 U g x ≤ Subgroup.normalizer (dS U g x : Set G) :=
    dF0_le_normalizer ((dS_le_dS2 U g x).trans (dS2_le_dX U x))
  obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_of_mem_sup hN he
  have hfs : f * s = s * f := dF0_comm_dX hf (dS2_le_dX U x (dS_le_dS2 U g x hs))
  have hs2 : s * s = 1 := S_sq D hCen hU hs
  have hf2 : f * f = 1 := dF0_sq D hCen hU hf
  calc s * f * (s * f) = s * (f * s) * f := by group
    _ = s * (s * f) * f := by rw [hfs]
    _ = (s * s) * (f * f) := by group
    _ = 1 := by rw [hs2, hf2, one_mul]

theorem S_mul_F0 (hAX : ∀ a ∈ omegaOneSub (conjSubgroup g U), a ∈ dX U x → a = 1)
    {s f : G} (hs : s ∈ dS U g x) (hf : f ∈ dF0 U g x)
    (ha : s * f ∈ omegaOneSub (conjSubgroup g U)) (h1 : s * f ≠ 1) :
    s ∉ dN U x ∧ f ≠ 1 := by
  have hsX : s ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hs)
  refine ⟨fun hsN => ?_, fun hf1 => ?_⟩
  · obtain ⟨β, hβ, hβ1⟩ := exists_U0_ne_one D
    have hβN : β ∈ dN U x := (show omegaOneSub U ≤ dN U x from le_sup_left) hβ
    have hβX : β ∈ dX U x := dN_le_dX U x hβN
    apply D.core.not_comm ha h1 hβ hβ1
    have hfβ : f * β = β * f := dF0_comm_dX hf hβX
    have hsβ : s * β = β * s := N_comm D hCen hU hsN hβN
    calc s * f * β = s * (f * β) := by group
      _ = s * (β * f) := by rw [hfβ]
      _ = (s * β) * f := by group
      _ = (β * s) * f := by rw [hsβ]
      _ = β * (s * f) := by group
  · subst hf1
    rw [mul_one] at ha h1
    exact h1 (hAX s ha hsX)

theorem dF0_inf_eq_bot {Z : Subgroup G} (hXZ : dX U x ≤ Z)
    (hAZ : ∀ a ∈ omegaOneSub (conjSubgroup g U), a ∈ Z → a = 1) : dF0 U g x ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨hf1, hfZ⟩ := Subgroup.mem_inf.mp hf
  obtain ⟨a, ha, y, hyS, rfl, -⟩ := mem_dF0 D hCen hU hf1
  have hyX : y ∈ dX U x := dS2_le_dX U x (dS_le_dS2 U g x hyS)
  have haZ : a ∈ Z := by
    have := Subgroup.mul_mem _ (hXZ hyX) hfZ
    simpa using this
  have ha1 := hAZ a ha haZ
  subst ha1
  have hmem : y⁻¹ * 1 ∈ dF0 U g x ⊓ dX U x :=
    Subgroup.mem_inf.mpr ⟨hf1, by simpa using (dX U x).inv_mem hyX⟩
  have := (dF0_inf_dX D hCen hU).le hmem
  exact this

theorem comm_C_N {c n : G} (hc : c ∈ conjSubgroup x U) (hn : n ∈ dN U x) :
    c * n * c⁻¹ * n⁻¹ ∈ omegaOneSub (conjSubgroup x U) := by
  by_cases hc0 : c ∈ omegaOneSub (conjSubgroup x U)
  · have hcN : c ∈ dN U x := (show omegaOneSub (conjSubgroup x U) ≤ dN U x from le_sup_right) hc0
    have h0 : c * n = n * c := N_comm D hCen hU hcN hn
    have h1 : c * n * c⁻¹ * n⁻¹ = 1 := by rw [h0]; group
    rw [h1]
    exact Subgroup.one_mem _
  · have hm : c * n * c⁻¹ ∈ dN U x := X_normalizes_N D hCen hU (C_le_dX U x hc) hn
    have hmn : c * n * c⁻¹ * n ∈ dN U x := Subgroup.mul_mem _ hm hn
    have hn2 : n * n = 1 := N_sq D hCen hU hn
    have hin : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
    have hcc : c * c ∈ omegaOneSub (conjSubgroup x U) := by
      rw [mem_omegaOneSub_iff (D.core.comm_conj' x)]
      refine ⟨Subgroup.mul_mem _ hc hc, ?_⟩
      calc c * c * (c * c) = c ^ 4 := mul_mul_mul_mul_eq_pow_four c
        _ = 1 := D.core.exp_conj x c hc
    have hccN : c * c ∈ dN U x :=
      (show omegaOneSub (conjSubgroup x U) ≤ dN U x from le_sup_right) hcc
    have hcc_n : c * c * n = n * (c * c) := N_comm D hCen hU hccN hn
    have hmm : c * (c * n * c⁻¹) * c⁻¹ = n := by
      calc c * (c * n * c⁻¹) * c⁻¹ = (c * c) * n * (c * c)⁻¹ := by group
        _ = n := by rw [hcc_n]; group
    have hnm : n * (c * n * c⁻¹) = (c * n * c⁻¹) * n := N_comm D hCen hU hn hm
    have hcomm_e : c * (c * n * c⁻¹ * n) = (c * n * c⁻¹ * n) * c := by
      calc c * (c * n * c⁻¹ * n) = (c * (c * n * c⁻¹) * c⁻¹) * (c * n * c⁻¹) * c := by group
        _ = n * (c * n * c⁻¹) * c := by rw [hmm]
        _ = (c * n * c⁻¹) * n * c := by rw [hnm]
    have he := cent_C D hCen hU hc hc0 hmn hcomm_e
    rw [hin]
    exact he

theorem comm_C_S {c s : G} (hc : c ∈ conjSubgroup x U) (hs : s ∈ dS U g x) :
    c * s * c⁻¹ * s⁻¹ ∈ omegaOneSub (conjSubgroup x U) := by
  have hs2 : s ∈ dS2 U x := dS_le_dS2 U g x hs
  obtain ⟨n, hn, c', hc', rfl⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) hs2
  have hcc' : Commute c' c := (D.core.comm_conj' x c hc c' hc').symm
  have hcc'' : c' * c⁻¹ * c'⁻¹ = c⁻¹ := by
    rw [(Commute.inv_right hcc').eq]
    group
  have e : c * (n * c') * c⁻¹ * (n * c')⁻¹ = c * n * c⁻¹ * n⁻¹ := by
    calc c * (n * c') * c⁻¹ * (n * c')⁻¹ = c * n * (c' * c⁻¹ * c'⁻¹) * n⁻¹ := by group
      _ = c * n * c⁻¹ * n⁻¹ := by rw [hcc'']
  rw [e]
  exact comm_C_N D hCen hU hc hn

theorem cent_S_C {c s : G} (hc : c ∈ conjSubgroup x U) (hc0 : c ∉ omegaOneSub (conjSubgroup x U))
    (hs : s ∈ dS U g x) (hcs : c * s = s * c) : s ∈ omegaOneSub (conjSubgroup x U) := by
  have hs2 : s ∈ dS2 U x := dS_le_dS2 U g x hs
  have hsA : ∀ a ∈ omegaOneSub (conjSubgroup g U), s * a = a * s := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs).2 a ha).symm
  obtain ⟨n, hn, c', hc', rfl⟩ := exists_mul_of_mem_sup
    (le_trans le_sup_right (D.le_normalizer hCen hU)) hs2
  have hcc' : c * c' = c' * c := D.core.comm_conj' x c hc c' hc'
  have hcn : c * n = n * c := by
    have h2 : (c * n) * c' = (n * c) * c' := by
      calc (c * n) * c' = c * (n * c') := by group
        _ = (n * c') * c := hcs
        _ = n * (c' * c) := by group
        _ = n * (c * c') := by rw [hcc']
        _ = (n * c) * c' := by group
    exact mul_right_cancel h2
  have hn0 : n ∈ omegaOneSub (conjSubgroup x U) := cent_C D hCen hU hc hc0 hn hcn
  have hsC : n * c' ∈ conjSubgroup x U := Subgroup.mul_mem _ (omegaOneSub_le _ hn0) hc'
  exact D.mem_C₀_of_comm hCen hU D.mem D.ne_one hsC (hsA α D.mem)

theorem comm_C_E {c e : G} (hc : c ∈ conjSubgroup x U) (he : e ∈ dS U g x ⊔ dF0 U g x) :
    c * e * c⁻¹ * e⁻¹ ∈ omegaOneSub (conjSubgroup x U) := by
  have hN : dF0 U g x ≤ Subgroup.normalizer (dS U g x : Set G) :=
    dF0_le_normalizer ((dS_le_dS2 U g x).trans (dS2_le_dX U x))
  obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_of_mem_sup hN he
  have hcf : f * c⁻¹ = c⁻¹ * f := dF0_comm_dX hf ((dX U x).inv_mem (C_le_dX U x hc))
  have e1 : c * (s * f) * c⁻¹ * (s * f)⁻¹ = c * s * c⁻¹ * s⁻¹ := by
    calc c * (s * f) * c⁻¹ * (s * f)⁻¹ = c * s * (f * c⁻¹) * f⁻¹ * s⁻¹ := by group
      _ = c * s * (c⁻¹ * f) * f⁻¹ * s⁻¹ := by rw [hcf]
      _ = c * s * c⁻¹ * s⁻¹ := by group
  rw [e1]
  exact comm_C_S D hCen hU hc hs

theorem cent_E {c e : G} (hc : c ∈ conjSubgroup x U) (hc0 : c ∉ omegaOneSub (conjSubgroup x U))
    (he : e ∈ dS U g x ⊔ dF0 U g x) (hce : c * e = e * c) :
    e ∈ omegaOneSub (conjSubgroup x U) ⊔ dF0 U g x := by
  have hN : dF0 U g x ≤ Subgroup.normalizer (dS U g x : Set G) :=
    dF0_le_normalizer ((dS_le_dS2 U g x).trans (dS2_le_dX U x))
  obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_of_mem_sup hN he
  have hfc : f * c = c * f := dF0_comm_dX hf (C_le_dX U x hc)
  have hcs : c * s = s * c := by
    have h2 : (c * s) * f = (s * c) * f := by
      calc (c * s) * f = c * (s * f) := by group
        _ = (s * f) * c := hce
        _ = s * (f * c) := by group
        _ = s * (c * f) := by rw [hfc]
        _ = (s * c) * f := by group
    exact mul_right_cancel h2
  have hs0 := cent_S_C D hCen hU hc hc0 hs hcs
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs0) (Subgroup.mem_sup_right hf)

theorem inf_dN_dS : dN U x ⊓ dS U g x = omegaOneSub (conjSubgroup x U) := by
  apply le_antisymm
  · intro n hn
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
    exact D.mem_C₀_of_mem_N hCen hU hn1 fun a ha =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn2).2 a ha
  · intro c hc
    have hcN : c ∈ dN U x := (show omegaOneSub (conjSubgroup x U) ≤ dN U x from le_sup_right) hc
    refine Subgroup.mem_inf.mpr ⟨hcN, Subgroup.mem_inf.mpr ⟨dN_le_dS2 U x hcN, ?_⟩⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => D.comm_C₀_A₀ hCen hU ha hc

theorem dS2_eq_sup : dS2 U x = dN U x ⊔ dS U g x := by
  apply le_antisymm
  · intro s hs
    obtain ⟨n, hn, s₁, hs₁, rfl⟩ := D.exists_eq_mul hCen hU hs
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hs₁)
  · exact sup_le (dN_le_dS2 U x) (dS_le_dS2 U g x)

theorem card_dS2 : Nat.card (dS2 U x) * Nat.card (omegaOneSub (conjSubgroup x U)) =
    Nat.card (dN U x) * Nat.card (conjSubgroup x U) := by
  have hNC : conjSubgroup x U ≤ Subgroup.normalizer (dN U x : Set G) :=
    fun c hc => D.le_normalizer hCen hU (C_le_dX U x hc)
  have h := card_sup_mul_card_inf_of_normalizes hNC
  have hinf : dN U x ⊓ conjSubgroup x U = omegaOneSub (conjSubgroup x U) := by
    rw [inf_comm]
    exact D.inf_N hCen hU
  rw [hinf] at h
  exact h

theorem card_dS : Nat.card (dS U g x) = Nat.card (conjSubgroup x U) := by
  have hNS : dS U g x ≤ Subgroup.normalizer (dN U x : Set G) := fun s hs =>
    D.le_normalizer hCen hU (dS2_le_dX U x (dS_le_dS2 U g x hs))
  have h1 := card_sup_mul_card_inf_of_normalizes hNS
  rw [← dS2_eq_sup D hCen hU, inf_dN_dS D hCen hU] at h1
  have h2 := card_dS2 D hCen hU
  have hpos : 0 < Nat.card (dN U x) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

theorem card_dN : Nat.card (dN U x) =
    Nat.card (omegaOneSub U) * Nat.card (omegaOneSub (conjSubgroup x U)) := by
  have hcomm : omegaOneSub (conjSubgroup x U) ≤ Subgroup.normalizer (omegaOneSub U : Set G) :=
    le_normalizer_of_comm fun c hc u hu =>
      N_comm D hCen hU ((show omegaOneSub (conjSubgroup x U) ≤ dN U x from le_sup_right) hc)
        ((show omegaOneSub U ≤ dN U x from le_sup_left) hu)
  have h := card_sup_mul_card_inf_of_normalizes hcomm
  have hinf : omegaOneSub U ⊓ omegaOneSub (conjSubgroup x U) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    have hmem : z ∈ U ⊓ conjSubgroup x U :=
      Subgroup.mem_inf.mpr ⟨omegaOneSub_le U hz1, omegaOneSub_le _ hz2⟩
    exact D.inf_UC.le hmem
  rw [hinf, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_dF0 (hAX : ∀ a ∈ omegaOneSub (conjSubgroup g U), a ∈ dX U x → a = 1) :
    Nat.card (dF0 U g x) = Nat.card (omegaOneSub (conjSubgroup g U)) := by
  have h1 := card_sup_mul_card_inf_of_normalizes
    (dF0_le_normalizer (U := U) (g := g) (x := x) (T := dX U x) le_rfl)
  have h2 := card_sup_mul_card_inf_of_normalizes (A0_le_normalizer_X D hCen hU)
  have hXF : dX U x ⊓ dF0 U g x = ⊥ := by
    rw [inf_comm]
    exact dF0_inf_dX D hCen hU
  have hXA : dX U x ⊓ omegaOneSub (conjSubgroup g U) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haX, haA⟩ := Subgroup.mem_inf.mp ha
    rw [Subgroup.mem_bot]
    exact hAX a haA haX
  have hsup : dX U x ⊔ dF0 U g x = dX U x ⊔ omegaOneSub (conjSubgroup g U) := by
    apply le_antisymm
    · exact sup_le le_sup_left inf_le_left
    · refine sup_le le_sup_left fun a ha => ?_
      obtain ⟨s, hs, f, hf, rfl⟩ := exists_mul_S_dF0 D hCen hU ha
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (dS2_le_dX U x (dS_le_dS2 U g x hs)))
        (Subgroup.mem_sup_right hf)
  rw [hsup, hXF, Subgroup.card_bot, mul_one] at h1
  rw [hXA, Subgroup.card_bot, mul_one] at h2
  have hpos : 0 < Nat.card (dX U x) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

theorem card_dE :
    Nat.card (dS U g x ⊔ dF0 U g x : Subgroup G) =
      Nat.card (dS U g x) * Nat.card (dF0 U g x) := by
  have h := card_sup_mul_card_inf_of_normalizes
    (dF0_le_normalizer (U := U) (g := g) (x := x) (T := dS U g x)
      ((dS_le_dS2 U g x).trans (dS2_le_dX U x)))
  rw [dS_inf_dF0 D hCen hU, Subgroup.card_bot, mul_one] at h
  exact h

end Inner

end Certificates34

end CFSG.CGT.PushingUpLit.SolKR2
