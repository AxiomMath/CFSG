module

public import CFSG.GH74.GLS.C3.Layer1.PU3Cover

public section

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Rank

variable {X : Type} [Group X] [Finite X]

theorem le_pRank_of_card_le {E : Subgroup X} (hE : CFSG.IsElementaryAbelian 2 ↥E) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card ↥E) : k ≤ CFSG.pRank 2 X := by
  have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hE
  refine ((Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hk.trans hcard.le)).trans ?_
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨E, hE, hcard⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := Nat.lt_two_pow_self.le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

theorem isElementaryAbelian_sup_card {A B : Subgroup X} (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) :
    CFSG.IsElementaryAbelian 2 ↥(A ⊔ B) ∧ Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  refine ⟨Th2.isElementaryAbelian_sup hA hB hcomm, ?_⟩
  have hnorm : A ≤ normalizer (B : Set X) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).symm
  have h := Th2.HY.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hAB, Subgroup.card_bot, mul_one] at h
  exact h

omit [Finite X] in
theorem inf_zpowers_eq_bot {E : Subgroup X} {c : X} (hc : orderOf c = 2) (hcE : c ∉ E) :
    E ⊓ zpowers c = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxE, hx⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : c ^ 2 = 1 := hc ▸ pow_orderOf_eq_one c
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, zpow_mul]
    simp [h2]
  · exfalso
    apply hcE
    have : c ^ (2 * k + 1) = c := by
      rw [zpow_add, zpow_mul, zpow_one]
      simp [h2]
    rwa [this] at hxE

theorem succ_le_pRank {E : Subgroup X} (hE : CFSG.IsElementaryAbelian 2 ↥E) {c : X}
    (hc : orderOf c = 2) (hcE : c ∉ E) (hcomm : ∀ e ∈ E, e * c = c * e) {k : ℕ}
    (hk : 2 ^ k ≤ Nat.card ↥E) : k + 1 ≤ CFSG.pRank 2 X := by
  have h2 : c ^ 2 = 1 := hc ▸ pow_orderOf_eq_one c
  have hZ : CFSG.IsElementaryAbelian 2 ↥(zpowers c) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one h2
  obtain ⟨hEZ, hcard⟩ := isElementaryAbelian_sup_card hE hZ (fun e he z hz => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (hcomm e he) n).eq) (inf_zpowers_eq_bot hc hcE)
  refine le_pRank_of_card_le hEZ ?_
  rw [hcard, Nat.card_zpowers, hc, pow_succ]
  exact Nat.mul_le_mul_right 2 hk

theorem five_le_pRank {A₁ A₂ F₁ F₂ : Subgroup X} (hA₁ : Pack.NonabSimple A₁)
    (hA₂ : Pack.NonabSimple A₂) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hF₁ : F₁ ≤ A₁) (hF₂ : F₂ ≤ A₂) (hE₁ : CFSG.IsElementaryAbelian 2 ↥F₁)
    (hE₂ : CFSG.IsElementaryAbelian 2 ↥F₂) (h₁ : 2 ^ 2 ≤ Nat.card ↥F₁) (h₂ : 2 ^ 2 ≤ Nat.card ↥F₂)
    {c : X} (hc : orderOf c = 2) (hc₁ : ∀ a ∈ A₁, a * c = c * a) (hc₂ : ∀ b ∈ A₂, b * c = c * b) :
    5 ≤ CFSG.pRank 2 X := by
  have hcomm' : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := fun a ha b hb => hcomm a (hF₁ ha) b (hF₂ hb)
  have hdisj : F₁ ⊓ F₂ = ⊥ :=
    le_bot_iff.1 ((inf_le_inf hF₁ hF₂).trans (Pack.inf_eq_bot_of_commute hA₁ hcomm).le)
  obtain ⟨hE, hcard⟩ := isElementaryAbelian_sup_card hE₁ hE₂ hcomm' hdisj
  refine succ_le_pRank (k := 4) hE hc ?_ ?_ ?_
  · intro hcF
    obtain ⟨a, ha, b, hb, hab⟩ := Pack.exists_mul_of_mem_sup hcomm' hcF
    have ha1 : a = 1 := by
      refine hA₁.eq_one_of_central (hF₁ ha) fun x hx => ?_
      have h1 : x * c = c * x := hc₁ x hx
      have h2 : x * b = b * x := hcomm x hx b (hF₂ hb)
      rw [hab] at h1
      have h3 : x * a * b = a * x * b :=
        calc x * a * b = x * (a * b) := by rw [mul_assoc]
          _ = a * b * x := h1
          _ = a * (b * x) := by rw [mul_assoc]
          _ = a * (x * b) := by rw [h2]
          _ = a * x * b := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    have hb1 : b = 1 := by
      refine hA₂.eq_one_of_central (hF₂ hb) fun x hx => ?_
      have h1 : x * c = c * x := hc₂ x hx
      rw [hab, ha1, one_mul] at h1
      exact h1.symm
    rw [hab, ha1, hb1, mul_one] at hc
    simp at hc
  · intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := Pack.exists_mul_of_mem_sup hcomm' he
    have h1 := hc₁ a (hF₁ ha)
    have h2 := hc₂ b (hF₂ hb)
    calc a * b * c = a * (b * c) := by rw [mul_assoc]
      _ = a * (c * b) := by rw [h2]
      _ = a * c * b := by rw [mul_assoc]
      _ = c * a * b := by rw [h1]
      _ = c * (a * b) := by rw [mul_assoc]
  · rw [hcard]
    calc 2 ^ 4 = 2 ^ 2 * 2 ^ 2 := by norm_num
      _ ≤ Nat.card ↥F₁ * Nat.card ↥F₂ := Nat.mul_le_mul h₁ h₂

theorem exists_involution_of_two_dvd {K : Subgroup X} (h : 2 ∣ Nat.card ↥K) :
    ∃ c ∈ K, orderOf c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

end Rank

section Struct

variable {G : Type} [Group G] [Finite G]

theorem Good.exists_four_group_img {M L : Subgroup G} (h : Good M L) :
    ∃ F : Subgroup (Mb M), F ≤ imgM M L ∧ CFSG.IsElementaryAbelian 2 ↥F ∧ 2 ^ 2 ≤ Nat.card ↥F := by
  obtain ⟨E, hEL, hE, hcard⟩ := Th2.CaseI.exists_elemAbelian_four h.rank
  have hEM : E ≤ M := hEL.trans h.comp.1
  obtain ⟨e⟩ := equiv_imgM hEM (CFSG.IsElementaryAbelian.isPGroup 2 ↥E)
  refine ⟨imgM M E, imgM_mono hEL, ?_, ?_⟩
  · have := hE
    have : CFSG.IsElementaryAbelian 2 ↥(E.subgroupOf M) := CFSG.IsElementaryAbelian.subgroupOf hEM
    exact CFSG.IsElementaryAbelian.map (A := E.subgroupOf M) (barMk ↥M)
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard

theorem two_dvd_card_of_comp {M L : Subgroup G} (h : IsPCompIn 2 M L) : 2 ∣ Nat.card ↥L := by
  obtain ⟨-, hsimple, a, b, hab⟩ := TwoThin.isQuasisimple_hat h
  have := hsimple
  exact ((CFSG.Walter.even_card_of_isSimpleGroup ⟨a, b, hab⟩).two_dvd.trans
    (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_quotient_dvd_card _)

def NoCentralizingInvolution (M L₁ L₂ : Subgroup G) : Prop :=
  ∀ c : Mb M, orderOf c = 2 →
    (∀ a ∈ imgM M L₁, a * c = c * a) →
    (∀ b ∈ imgM M L₂, b * c = c * b) → False

theorem false_of_centralizing_involution (hGen : Gen4 G) {M L₁ L₂ : Subgroup G} (h₁ : Good M L₁)
    (h₂ : Good M L₂) (hne : L₁ ≠ L₂) {c : Mb M} (hc : orderOf c = 2)
    (hc₁ : ∀ a ∈ imgM M L₁, a * c = c * a) (hc₂ : ∀ b ∈ imgM M L₂, b * c = c * b) : False := by
  have hX : Gen4 (Mb M) := Gen4.quotient _ (Gen4.subgroup M hGen)
  obtain ⟨F₁, hF₁, hE₁, hF₁c⟩ := h₁.exists_four_group_img
  obtain ⟨F₂, hF₂, hE₂, hF₂c⟩ := h₂.exists_four_group_img
  have h5 := five_le_pRank ⟨h₁.imgM_simple, h₁.imgM_nonab⟩ ⟨h₂.imgM_simple, h₂.imgM_nonab⟩
    (imgM_comm_of_ne h₁.comp h₂.comp hne) hF₁ hF₂ hE₁ hE₂ hF₁c hF₂c hc hc₁ hc₂
  have h4 := hX.pRank_two_le
  omega

theorem only_of_good_of_noCentral {M L₁ L₂ : Subgroup G}
    (hno : NoCentralizingInvolution M L₁ L₂) (h₁ : Good M L₁) (h₂ : Good M L₂)
    (hne : L₁ ≠ L₂) {L' : Subgroup G}
    (hL' : IsPCompIn 2 M L') : L' = L₁ ∨ L' = L₂ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn₁, hn₂⟩ := hcon
  obtain ⟨j, hjL, hj2⟩ := exists_involution_of_two_dvd (two_dvd_card_of_comp hL')
  have hjM : j ∈ M := hL'.1 hjL
  have hc2 : orderOf (barMk ↥M ⟨j, hjM⟩) = 2 :=
    TwoThin.orderOf_barMk (by rw [Subgroup.orderOf_mk]; exact hj2)
  have hcL' : barMk ↥M ⟨j, hjM⟩ ∈ imgM M L' := mem_imgM_iff.2 ⟨⟨j, hjM⟩, hjL, rfl⟩
  exact hno _ hc2
    (fun a ha => (imgM_comm_of_ne hL' h₁.comp hn₁ _ hcL' a ha).symm)
    (fun b hb => (imgM_comm_of_ne hL' h₂.comp hn₂ _ hcL' b hb).symm)

theorem only_of_good (hGen : Gen4 G) {M L₁ L₂ : Subgroup G} (h₁ : Good M L₁) (h₂ : Good M L₂)
    (hne : L₁ ≠ L₂) {L' : Subgroup G} (hL' : IsPCompIn 2 M L') : L' = L₁ ∨ L' = L₂ :=
  only_of_good_of_noCentral
    (fun c hc hc₁ hc₂ => false_of_centralizing_involution hGen h₁ h₂ hne hc hc₁ hc₂)
    h₁ h₂ hne hL'

omit [Finite G] in
theorem map_conj_imgM {M : Subgroup G} (m : ↥M) (L : Subgroup G) :
    (imgM M L).map (MulAut.conj (barMk ↥M m)).toMonoidHom = imgM M (cj (m : G) L) := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨l, hl, rfl⟩ := mem_imgM_iff.1 hy
    refine mem_imgM_iff.2 ⟨m * l * m⁻¹, (mem_cj_iff' (m : G) L (l : G)).2 hl, ?_⟩
    simp [map_mul, map_inv, MulAut.conj_apply]
  · intro hw
    obtain ⟨n, hn, rfl⟩ := mem_imgM_iff.1 hw
    refine ⟨barMk ↥M (m⁻¹ * n * m),
      mem_imgM_iff.2 ⟨m⁻¹ * n * m, (mem_cj_iff (m : G) L n).1 hn, rfl⟩, ?_⟩
    have e : m * (m⁻¹ * n * m) * m⁻¹ = n := by group
    show barMk ↥M m * barMk ↥M (m⁻¹ * n * m) * (barMk ↥M m)⁻¹ = barMk ↥M n
    rw [← map_inv, ← map_mul, ← map_mul, e]

theorem isPCompIn_cj_of_mem {M L : Subgroup G} (h : IsPCompIn 2 M L) {m : G} (hm : m ∈ M) :
    IsPCompIn 2 M (cj m L) := by
  have := Stage1.Thm2.Recip.isPCompIn_map_conj h m
  rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hm] at this

theorem perf_of_good_of_noCentral {M L₁ L₂ : Subgroup G}
    (hno : NoCentralizingInvolution M L₁ L₂) (h₁ : Good M L₁) (h₂ : Good M L₂)
    (hne : L₁ ≠ L₂)
    (hOut₁ : Group.IsSolvable (Outer (kBar L₁))) (hOut₂ : Group.IsSolvable (Outer (kBar L₂))) :
    ∀ Y : Subgroup G, Y ≤ M → ⁅Y, Y⁆ = Y → Y ≤ L₁ ⊔ L₂ ⊔ pPrimeCoreOf 2 M := by
  have honly : ∀ L' : Subgroup G, IsPCompIn 2 M L' → L' = L₁ ∨ L' = L₂ := fun _ hL' =>
    only_of_good_of_noCentral hno h₁ h₂ hne hL'
  have hcomm := imgM_comm_of_ne h₁.comp h₂.comp hne
  have hA : Pack.NonabSimple (imgM M L₁) := ⟨h₁.imgM_simple, h₁.imgM_nonab⟩
  have hB : Pack.NonabSimple (imgM M L₂) := ⟨h₂.imgM_simple, h₂.imgM_nonab⟩
  have hperm : ∀ x : Mb M,
      ((imgM M L₁).map (MulAut.conj x).toMonoidHom = imgM M L₁ ∧
        (imgM M L₂).map (MulAut.conj x).toMonoidHom = imgM M L₂) ∨
      ((imgM M L₁).map (MulAut.conj x).toMonoidHom = imgM M L₂ ∧
        (imgM M L₂).map (MulAut.conj x).toMonoidHom = imgM M L₁) := by
    intro x
    obtain ⟨m, rfl⟩ := barMk_surjective (Y := ↥M) x
    rw [map_conj_imgM, map_conj_imgM]
    rcases honly _ (isPCompIn_cj_of_mem h₁.comp m.2) with e₁ | e₁ <;>
      rcases honly _ (isPCompIn_cj_of_mem h₂.comp m.2) with e₂ | e₂
    · exact absurd (cj_injective (m : G) (e₁.trans e₂.symm)) hne
    · left
      rw [e₁, e₂]
      exact ⟨rfl, rfl⟩
    · right
      rw [e₁, e₂]
      exact ⟨rfl, rfl⟩
    · exact absurd (cj_injective (m : G) (e₁.trans e₂.symm)) hne
  have hS : ∀ g : Mb M, (imgM M L₁ ⊔ imgM M L₂).map (MulAut.conj g).toMonoidHom =
      imgM M L₁ ⊔ imgM M L₂ := by
    intro g
    rw [Subgroup.map_sup]
    rcases hperm g with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [e₁, e₂]
    · rw [e₁, e₂, sup_comm]
  have hSconj : ∀ g : Mb M, ∀ s ∈ imgM M L₁ ⊔ imgM M L₂,
      g * s * g⁻¹ ∈ imgM M L₁ ⊔ imgM M L₂ := by
    intro g s hs
    have : (MulAut.conj g).toMonoidHom s ∈
        (imgM M L₁ ⊔ imgM M L₂).map (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hs
    rw [hS g] at this
    simpa [MulAut.conj_apply] using this
  have hcent : ∀ x : Mb M, (∀ a ∈ imgM M L₁, x * a = a * x) → (∀ b ∈ imgM M L₂, x * b = b * x) →
      x = 1 := by
    intro x hxA hxB
    set C : Subgroup (Mb M) :=
      Subgroup.centralizer ((imgM M L₁ ⊔ imgM M L₂ : Subgroup (Mb M)) : Set (Mb M)) with hC
    have hCnormal : C.Normal := ⟨fun n hn g => by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : g⁻¹ * s * g ∈ imgM M L₁ ⊔ imgM M L₂ := by simpa using hSconj g⁻¹ s hs
      have hn' := Subgroup.mem_centralizer_iff.1 hn _ hs'
      calc s * (g * n * g⁻¹) = g * ((g⁻¹ * s * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * s * g)) * g⁻¹ := by rw [hn']
        _ = (g * n * g⁻¹) * s := by group⟩
    have hCodd : Odd (Nat.card C) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨c, hcC, hc2⟩ := exists_involution_of_two_dvd hev.two_dvd
      exact hno _ hc2
        (fun a ha => Subgroup.mem_centralizer_iff.1 hcC a (Subgroup.mem_sup_left ha))
        (fun b hb => Subgroup.mem_centralizer_iff.1 hcC b (Subgroup.mem_sup_right hb))
    have hCbot : C = ⊥ := by
      have hle : C ≤ pPrimeCore 2 (Mb M) :=
        CFSG.GroupTheory.le_pPrimeCore_of_normal hCnormal (Nat.coprime_two_left.2 hCodd)
      rw [pPrimeCore_quotient_eq_bot ↥M] at hle
      exact le_bot_iff.1 hle
    have hxC : x ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro s hs
      have hsup : imgM M L₁ ⊔ imgM M L₂ ≤ Subgroup.centralizer ({x} : Set (Mb M)) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hxA a ha).symm)
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hxB b hb).symm)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hs)
    rw [hCbot] at hxC
    exact Subgroup.mem_bot.1 hxC
  have hOA : Group.IsSolvable (Outer ↥(imgM M L₁)) := by
    obtain ⟨e⟩ := imgM_equiv_kBar_self h₁.comp
    have := hOut₁
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  have hOB : Group.IsSolvable (Outer ↥(imgM M L₂)) := by
    obtain ⟨e⟩ := imgM_equiv_kBar_self h₂.comp
    have := hOut₂
    exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm
  intro Y hYM hY
  have hYperf : ⁅imgM M Y, imgM M Y⁆ = imgM M Y := by
    unfold imgM
    rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hYM hY]
  have hle := Pack.perfect_le_sup hA hB hcomm hperm hcent hOA hOB hYperf
  rw [← imgM_sup h₁.comp.1 h₂.comp.1] at hle
  intro y hy
  have hyM : y ∈ M := hYM hy
  have hmem : barMk ↥M ⟨y, hyM⟩ ∈ imgM M (L₁ ⊔ L₂) := hle (mem_imgM_iff.2 ⟨⟨y, hyM⟩, hy, rfl⟩)
  obtain ⟨l, hl, hly⟩ := mem_imgM_iff.1 hmem
  have h1 : barMk ↥M (l⁻¹ * ⟨y, hyM⟩) = 1 := by rw [map_mul, map_inv, hly, inv_mul_cancel]
  have h2 : ((l⁻¹ * ⟨y, hyM⟩ : ↥M) : G) ∈ pPrimeCoreOf 2 M :=
    (barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1
  have h3 : y = (l : G) * ((l⁻¹ * ⟨y, hyM⟩ : ↥M) : G) := by simp
  rw [h3]
  exact Subgroup.mul_mem_sup hl h2

theorem perf_of_good (hGen : Gen4 G) {M L₁ L₂ : Subgroup G} (h₁ : Good M L₁) (h₂ : Good M L₂)
    (hne : L₁ ≠ L₂) (_hswap : ∃ s ∈ M, cj s L₁ = L₂)
    (hOut₁ : Group.IsSolvable (Outer (kBar L₁))) (hOut₂ : Group.IsSolvable (Outer (kBar L₂))) :
    ∀ Y : Subgroup G, Y ≤ M → ⁅Y, Y⁆ = Y → Y ≤ L₁ ⊔ L₂ ⊔ pPrimeCoreOf 2 M :=
  perf_of_good_of_noCentral
    (fun c hc hc₁ hc₂ => false_of_centralizing_involution hGen h₁ h₂ hne hc hc₁ hc₂)
    h₁ h₂ hne hOut₁ hOut₂

end Struct

end CFSG.GH74.GLS.PU3
