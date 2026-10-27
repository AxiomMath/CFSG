module

public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace LocBalL3Abs

variable {X : Type} [Group X]

structure Layer (t : X) (S : Subgroup X) : Prop where
  mem : t ∈ S
  quasisimple : CFSG.IsQuasisimple ↥S
  le_centralizer : S ≤ centralizer ({t} : Set X)
  conj_mem : ∀ x ∈ centralizer ({t} : Set X), ∀ s ∈ S, x * s * x⁻¹ ∈ S
  commutator_mem : ∀ x ∈ centralizer ({t} : Set X), ∀ y ∈ centralizer ({t} : Set X), ⁅x, y⁆ ∈ S
  center_le : ∀ s ∈ S, (∀ s' ∈ S, s' * s = s * s') → s = 1 ∨ s = t

theorem comm_mul_right {G : Type*} [Group G] (r s z : G) (hz : s * z = z * s) :
    ⁅r * z, s⁆ = ⁅r, s⁆ := by
  have h : z * s * z⁻¹ = s := by rw [mul_inv_eq_iff_eq_mul]; exact hz.symm
  calc ⁅r * z, s⁆ = r * (z * s * z⁻¹) * r⁻¹ * s⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅r, s⁆ := by rw [h]; rfl

theorem comm_mul_left {G : Type*} [Group G] (r s z : G) (hz : r * z = z * r) :
    ⁅r, s * z⁆ = ⁅r, s⁆ := by
  have h : z * r⁻¹ * z⁻¹ = r⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    calc z * r⁻¹ = r⁻¹ * (r * z) * r⁻¹ := by group
      _ = r⁻¹ * (z * r) * r⁻¹ := by rw [hz]
      _ = r⁻¹ * z := by group
  calc ⁅r, s * z⁆ = r * s * (z * r⁻¹ * z⁻¹) * s⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅r, s⁆ := by rw [h]; rfl

theorem Layer.meet_eq_one {t : X} {S : Subgroup X} (hS : Layer t S) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {Q : Subgroup X} (hQn : ∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q, w * q * w⁻¹ ∈ Q)
    (hQo : Odd (Nat.card ↥Q)) : ∀ x ∈ Q, x ∈ S → x = 1 := by
  have ht : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have htQ : t ∉ Q := by
    intro h
    have h1 := Subgroup.orderOf_dvd_natCard Q h
    rw [ht] at h1
    exact (Nat.not_even_iff_odd.mpr hQo) (even_iff_two_dvd.mpr h1)
  let R : Subgroup ↥S := Q.comap S.subtype
  have hRn : R.Normal := ⟨fun n hn g => by
    have hg : (g : X) ∈ centralizer ({t} : Set X) := hS.le_centralizer g.2
    exact hQn _ hg _ hn⟩
  let π := QuotientGroup.mk' (Subgroup.center ↥S)
  have hRπ : (R.map π).Normal := Subgroup.Normal.map hRn π (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hS.quasisimple.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.map π) with hbot | htop
  · intro x hxQ hxS
    have hxR : (⟨x, hxS⟩ : ↥S) ∈ R := hxQ
    have hker : π ⟨x, hxS⟩ = 1 := by
      have : π ⟨x, hxS⟩ ∈ R.map π := ⟨_, hxR, rfl⟩
      rw [hbot] at this
      exact this
    have hcen : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hker
    have hcen' : ∀ s' ∈ S, s' * x = x * s' := fun s' hs' =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨s', hs'⟩)
    rcases hS.center_le x hxS hcen' with h | h
    · exact h
    · exact absurd (h ▸ hxQ) htQ
  · exfalso
    have hcomm : (commutator ↥S) ≤ R := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have ha : π a ∈ R.map π := by rw [htop]; trivial
      have hb : π b ∈ R.map π := by rw [htop]; trivial
      obtain ⟨r, hr, hra⟩ := ha
      obtain ⟨r', hr', hrb⟩ := hb
      have hza : r⁻¹ * a ∈ Subgroup.center ↥S := by
        rw [← QuotientGroup.eq]; exact hra
      have hzb : r'⁻¹ * b ∈ Subgroup.center ↥S := by
        rw [← QuotientGroup.eq]; exact hrb
      have ea : a = r * (r⁻¹ * a) := by group
      have eb : b = r' * (r'⁻¹ * b) := by group
      have hza' := Subgroup.mem_center_iff.mp hza
      have hzb' := Subgroup.mem_center_iff.mp hzb
      have h1 : ⁅a, b⁆ = ⁅r, r'⁆ := by
        rw [ea, eb, comm_mul_right _ _ _ (hza' _), comm_mul_left _ _ _ (hzb' _)]
      rw [h1]
      simp only [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hr hr') (R.inv_mem hr)) (R.inv_mem hr')
    have hperf : commutator ↥S = ⊤ := hS.quasisimple.1.commutator_eq_top
    have htR : (⟨t, hS.mem⟩ : ↥S) ∈ R := by
      apply hcomm
      rw [hperf]; trivial
    exact htQ htR


theorem Layer.odd_normal_central {t : X} {S : Subgroup X} (hS : Layer t S) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) {Q : Subgroup X} (hQC : Q ≤ centralizer ({t} : Set X))
    (hQn : ∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) (hQo : Odd (Nat.card ↥Q)) :
    ∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q, w * q = q * w := by
  intro w hw q hq
  have h1 : w * q * w⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQn w hw q hq) (Q.inv_mem hq)
  have h2 : w * q * w⁻¹ * q⁻¹ ∈ S := hS.commutator_mem w hw q (hQC hq)
  have h3 := hS.meet_eq_one ht2 ht1 hQn hQo _ h1 h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem comm_twist {G : Type*} [Group G] (u₁ u₂ w₁ w₂ : G) (h11 : w₁ * u₁ = u₁ * w₁)
    (h12 : w₂ * u₁ = u₁ * w₂) (h21 : w₁ * u₂ = u₂ * w₁) (h22 : w₂ * u₂ = u₂ * w₂)
    (h : u₁ * u₂ = u₂ * u₁) : ⁅u₁ * w₁, u₂ * w₂⁆ = ⁅w₁, w₂⁆ := by
  have hb : (u₂ * w₂) * u₁ = u₁ * (u₂ * w₂) := by
    rw [mul_assoc, h12, ← mul_assoc, ← h, mul_assoc]
  rw [← h11, comm_mul_right _ _ _ hb, ← h22, comm_mul_left _ _ _ h21]


theorem conj_injective (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  apply hZ t
  intro g
  have h2 := congrArg (fun f : MulAut X => f g) ht
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem aut_mul_conj_mul_inv (σ : MulAut X) (w : X) :
    σ * MulAut.conj w * σ⁻¹ = MulAut.conj (σ w) := by
  ext x
  simp [MulAut.conj_apply]


theorem oddCore_props {G : Type*} [Group G] [Finite G] (b : G) :
    involutionOddCore b ≤ centralizer ({b} : Set G) ∧
    (∀ g ∈ centralizer ({b} : Set G), ∀ n ∈ involutionOddCore b,
      g * n * g⁻¹ ∈ involutionOddCore b) ∧
    Odd (Nat.card ↥(involutionOddCore b)) := by
  refine ⟨involutionOddCore_le_centralizer b, ?_, ?_⟩
  · intro g hg n hn
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    refine ⟨⟨g, hg⟩ * n₀ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance n₀ hn₀ ⟨g, hg⟩
  · unfold involutionOddCore
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), oddCore_eq_pPrimeCore]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card


section Embedding

variable {H : Subgroup (MulAut X)}

@[expose] def phi (hH : (MulAut.conj : X →* MulAut X).range ≤ H) : X →* ↥H :=
  (MulAut.conj : X →* MulAut X).codRestrict H (fun x => hH ⟨x, rfl⟩)

theorem coe_phi (hH : (MulAut.conj : X →* MulAut X).range ≤ H) (x : X) :
    ((phi hH x : ↥H) : MulAut X) = MulAut.conj x := rfl

theorem phi_injective (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) : Function.Injective (phi hH) :=
  fun _ _ h => conj_injective hZ (congrArg Subtype.val h)

end Embedding

section Twist

variable [Finite X] {H : Subgroup (MulAut X)}

theorem Layer.twist (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hH : (MulAut.conj : X →* MulAut X).range ≤ H) {t : X} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    {S : Subgroup X} (hS : Layer t S) {c : ↥H} (hc : c ∈ involutionOddCore (phi hH t)) :
    (c : MulAut X) t = t ∧
    (∀ w ∈ centralizer ({t} : Set X), w * w = 1 → (c : MulAut X) w = w) ∧
    (∀ w ∈ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆, (c : MulAut X) w = w) := by
  obtain ⟨hN1, hN2, hN3⟩ := oddCore_props (phi hH t)
  have hφinj := phi_injective hZ hH
  set ĉ : MulAut X := (c : MulAut X) with hĉ
  have hct : c * phi hH t = phi hH t * c := Subgroup.mem_centralizer_singleton_iff.mp (hN1 hc)
  have hct' : ĉ * MulAut.conj t * ĉ⁻¹ = MulAut.conj t := by
    have := congrArg (fun g : ↥H => (g : MulAut X)) hct
    simp only [Subgroup.coe_mul, coe_phi] at this
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hfix : ĉ t = t := by
    apply conj_injective hZ
    rw [← aut_mul_conj_mul_inv, hct']
  let Q₀ : Subgroup X := (involutionOddCore (phi hH t)).comap (phi hH)
  have hphiC : ∀ w ∈ centralizer ({t} : Set X), phi hH w ∈ centralizer ({phi hH t} : Set ↥H) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    rw [← map_mul, ← map_mul, hw]
  have hQC : Q₀ ≤ centralizer ({t} : Set X) := by
    intro q hq
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hN1 hq)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hφinj
    rw [map_mul, map_mul]
    exact h1
  have hQn : ∀ w ∈ centralizer ({t} : Set X), ∀ q ∈ Q₀, w * q * w⁻¹ ∈ Q₀ := by
    intro w hw q hq
    have := hN2 (phi hH w) (hphiC w hw) (phi hH q) hq
    show phi hH (w * q * w⁻¹) ∈ involutionOddCore (phi hH t)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hQo : Odd (Nat.card ↥Q₀) := by
    have h1 : Q₀.map (phi hH) ≤ involutionOddCore (phi hH t) := Subgroup.map_comap_le _ _
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective hφinj] at h2
    exact Odd.of_dvd_nat hN3 h2
  have hcen := hS.odd_normal_central ht2 ht1 hQC hQn hQo
  have hzmem : ∀ w ∈ centralizer ({t} : Set X), ĉ w * w⁻¹ ∈ Q₀ := by
    intro w hw
    have h1 : phi hH (ĉ w * w⁻¹) = c * (phi hH w * c⁻¹ * (phi hH w)⁻¹) := by
      apply Subtype.ext
      simp only [coe_phi, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [← aut_mul_conj_mul_inv ĉ w, hĉ]
      group
    show phi hH (ĉ w * w⁻¹) ∈ involutionOddCore (phi hH t)
    rw [h1]
    exact Subgroup.mul_mem _ hc (hN2 _ (hphiC w hw) _ (Subgroup.inv_mem _ hc))
  have hcomm_inv : ∀ w ∈ centralizer ({t} : Set X), ∀ u ∈ Q₀, u * w⁻¹ = w⁻¹ * u := by
    intro w hw u hu
    have h1 := hcen w hw u hu
    calc u * w⁻¹ = w⁻¹ * (w * u) * w⁻¹ := by group
      _ = w⁻¹ * (u * w) * w⁻¹ := by rw [h1]
      _ = w⁻¹ * u := by group
  have hzmul : ∀ w₁ ∈ centralizer ({t} : Set X), ∀ w₂ ∈ centralizer ({t} : Set X),
      ĉ (w₁ * w₂) * (w₁ * w₂)⁻¹ = (ĉ w₁ * w₁⁻¹) * (ĉ w₂ * w₂⁻¹) := by
    intro w₁ h₁ w₂ h₂
    have hu := hcomm_inv w₁ h₁ _ (hzmem w₂ h₂)
    calc ĉ (w₁ * w₂) * (w₁ * w₂)⁻¹ = ĉ w₁ * ((ĉ w₂ * w₂⁻¹) * w₁⁻¹) := by rw [map_mul]; group
      _ = ĉ w₁ * (w₁⁻¹ * (ĉ w₂ * w₂⁻¹)) := by rw [hu]
      _ = (ĉ w₁ * w₁⁻¹) * (ĉ w₂ * w₂⁻¹) := by group
  have hinv : ∀ w ∈ centralizer ({t} : Set X), w * w = 1 → ĉ w = w := by
    intro w hw hww
    have hu := hzmem w hw
    have h1 := hzmul w hw w hw
    rw [hww, inv_one, mul_one, map_one] at h1
    by_contra hne
    have hne' : ĉ w * w⁻¹ ≠ 1 := fun h => hne (by rwa [mul_inv_eq_one] at h)
    have h2 : orderOf (ĉ w * w⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact h1.symm) hne'
    have h3 := Subgroup.orderOf_dvd_natCard Q₀ hu
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hQo) (even_iff_two_dvd.mpr h3)
  refine ⟨hfix, hinv, ?_⟩
  let K : Subgroup X := (ĉ : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X)
  have hK : ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro w₁ h₁ w₂ h₂
    obtain ⟨u₁, hu₁def⟩ : ∃ u₁, u₁ = ĉ w₁ * w₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂def⟩ : ∃ u₂, u₂ = ĉ w₂ * w₂⁻¹ := ⟨_, rfl⟩
    have hu₁ : u₁ ∈ Q₀ := hu₁def ▸ hzmem w₁ h₁
    have hu₂ : u₂ ∈ Q₀ := hu₂def ▸ hzmem w₂ h₂
    have e1 : ĉ w₁ = u₁ * w₁ := by rw [hu₁def]; group
    have e2 : ĉ w₂ = u₂ * w₂ := by rw [hu₂def]; group
    show ĉ ⁅w₁, w₂⁆ = ⁅w₁, w₂⁆
    rw [map_commutatorElement, e1, e2]
    exact comm_twist u₁ u₂ w₁ w₂ (hcen w₁ h₁ u₁ hu₁) (hcen w₂ h₂ u₁ hu₁) (hcen w₁ h₁ u₂ hu₂)
      (hcen w₂ h₂ u₂ hu₂) (hcen u₁ (hQC hu₁) u₂ hu₂)
  exact fun w hw => hK hw


@[expose] def GenPair (E : Subgroup X) : Prop :=
  ∃ t₁ ∈ E, ∃ t₂ ∈ E, t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₂ * t₂ = 1 ∧ t₂ ≠ 1 ∧ t₁ ≠ t₂ ∧
    ∃ B₁ B₂ : Subgroup X, B₁ ≤ centralizer ({t₁} : Set X) ∧ B₂ ≤ centralizer ({t₂} : Set X) ∧
      ⁅B₁, B₁⁆ = B₁ ∧ ⁅B₂, B₂⁆ = B₂ ∧ B₁ ⊔ B₂ = ⊤

theorem locBal32_of_layers (hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1)
    (hL : ∀ t : X, t * t = 1 → t ≠ 1 → ∃ S : Subgroup X, Layer t S)
    (hG : ∀ E : Subgroup X, (∀ e ∈ E, e * e = 1) → Nat.card ↥E = 4 → GenPair E)
    (B : Subgroup X) (hB : ∀ b ∈ B, b * b = 1) :
    IsLocBal32 X (B.map (MulAut.conj : X →* MulAut X)) := by
  intro H hH hBH
  have hφinj := phi_injective hZ hH
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h1 := hB _ (B.mul_mem ha hb)
    have h2 := hB a ha
    have h3 := hB b hb
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    calc a * b = (a * b)⁻¹ := e3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [e1, e2]
  refine ⟨?_, ?_⟩
  · intro b hb hb1 c hc b' hb'
    obtain ⟨t, htB, hbt⟩ := Subgroup.mem_subgroupOf.mp hb
    obtain ⟨t', ht'B, hb't'⟩ := Subgroup.mem_subgroupOf.mp hb'
    have hbphi : b = phi hH t := Subtype.ext hbt.symm
    have hb'phi : b' = phi hH t' := Subtype.ext hb't'.symm
    have ht2 := hB t htB
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hb1 (by rw [hbphi, map_one])
    obtain ⟨S, hS⟩ := hL t ht2 ht1
    rw [hbphi] at hc
    obtain ⟨-, hinv, -⟩ := hS.twist hZ hH ht2 ht1 hc
    have hfix : (c : MulAut X) t' = t' :=
      hinv t' (Subgroup.mem_centralizer_singleton_iff.mpr (hBc t' ht'B t htB)) (hB t' ht'B)
    rw [hb'phi, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_phi]
    have := aut_mul_conj_mul_inv (c : MulAut X) t'
    rw [hfix, mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro D hD hcard hsq
    let E' : Subgroup X := D.comap (phi hH)
    have hDmem : ∀ d ∈ D, ∃ x ∈ B, phi hH x = d := by
      intro d hd
      obtain ⟨x, hxB, hx⟩ := Subgroup.mem_subgroupOf.mp (hD hd)
      exact ⟨x, hxB, Subtype.ext hx⟩
    have hDeq : E'.map (phi hH) = D := by
      ext d
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hd
        obtain ⟨x, hxB, hx⟩ := hDmem d hd
        refine ⟨x, ?_, hx⟩
        show phi hH x ∈ D
        rw [hx]
        exact hd
    have hE'sq : ∀ e ∈ E', e * e = 1 := by
      intro e he
      apply hφinj
      rw [map_mul, map_one]
      exact hsq _ he
    have hE'card : Nat.card ↥E' = 4 := by
      rw [← hcard, ← hDeq, Subgroup.card_map_of_injective hφinj]
    obtain ⟨t₁, ht₁, t₂, ht₂, ht₁2, ht₁1, ht₂2, ht₂1, -, B₁, B₂, hB₁, hB₂, hP₁, hP₂, hgen⟩ :=
      hG E' hE'sq hE'card
    obtain ⟨S₁, hS₁⟩ := hL t₁ ht₁2 ht₁1
    obtain ⟨S₂, hS₂⟩ := hL t₂ ht₂2 ht₂1
    rw [eq_bot_iff]
    intro c hc
    have hc₁ : c ∈ involutionOddCore (phi hH t₁) :=
      deltaCore_le_involutionOddCore (d := phi hH t₁) ht₁
        (fun h => ht₁1 (hφinj (by rw [h, map_one]))) hc
    have hc₂ : c ∈ involutionOddCore (phi hH t₂) :=
      deltaCore_le_involutionOddCore (d := phi hH t₂) ht₂
        (fun h => ht₂1 (hφinj (by rw [h, map_one]))) hc
    obtain ⟨-, -, hcomm₁⟩ := hS₁.twist hZ hH ht₁2 ht₁1 hc₁
    obtain ⟨-, -, hcomm₂⟩ := hS₂.twist hZ hH ht₂2 ht₂1 hc₂
    let K : Subgroup X := ((c : MulAut X)).toMonoidHom.eqLocus (MonoidHom.id X)
    have hK₁ : B₁ ≤ K := by
      intro w hw
      rw [← hP₁] at hw
      exact hcomm₁ w (Subgroup.commutator_mono hB₁ hB₁ hw)
    have hK₂ : B₂ ≤ K := by
      intro w hw
      rw [← hP₂] at hw
      exact hcomm₂ w (Subgroup.commutator_mono hB₂ hB₂ hw)
    have hKtop : (⊤ : Subgroup X) ≤ K := by
      rw [← hgen]
      exact sup_le hK₁ hK₂
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact hKtop (Subgroup.mem_top x)

end Twist

section Transport

variable {Y : Type} [Group Y]

theorem Layer.map (e : X ≃* Y) {t : X} {S : Subgroup X} (h : Layer t S) :
    Layer (e t) (S.map e.toMonoidHom) where
  mem := ⟨t, h.mem, rfl⟩
  quasisimple := CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e S) h.quasisimple
  le_centralizer := by
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hs)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e this
  conj_mem := by
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hx' : e.symm x ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
    refine ⟨e.symm x * s * (e.symm x)⁻¹, h.conj_mem _ hx' s hs, ?_⟩
    simp
  commutator_mem := by
    intro x hx y hy
    have hx' : e.symm x ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
    have hy' : e.symm y ∈ centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
    refine ⟨⁅e.symm x, e.symm y⁆, h.commutator_mem _ hx' _ hy', ?_⟩
    simp
  center_le := by
    rintro _ ⟨s, hs, rfl⟩ hcen
    have hs' : ∀ s' ∈ S, s' * s = s * s' := by
      intro s' hs'
      apply e.injective
      rw [map_mul, map_mul]
      exact hcen (e s') ⟨s', hs', rfl⟩
    rcases h.center_le s hs hs' with h1 | h1
    · left
      rw [MulEquiv.coe_toMonoidHom, h1, map_one]
    · right
      rw [MulEquiv.coe_toMonoidHom, h1]

theorem GenPair.map (e : X ≃* Y) {E : Subgroup X} (h : GenPair E) :
    GenPair (E.map e.toMonoidHom) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, n1, h2, n2, h12, B₁, B₂, hB₁, hB₂, hP₁, hP₂, hgen⟩ := h
  have hmulinv : ∀ a : X, e a * e a = 1 ↔ a * a = 1 := by
    intro a
    rw [← map_mul]
    exact ⟨fun h => e.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hne : ∀ a : X, e a ≠ 1 ↔ a ≠ 1 := by
    intro a
    exact not_congr (map_eq_one_iff e e.injective)
  have hcent : ∀ (a : X) (B : Subgroup X), B ≤ centralizer ({a} : Set X) →
      B.map e.toMonoidHom ≤ centralizer ({e a} : Set Y) := by
    rintro a B hB _ ⟨b, hb, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hB hb)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e this
  have hperf : ∀ B : Subgroup X, ⁅B, B⁆ = B → ⁅B.map e.toMonoidHom, B.map e.toMonoidHom⁆ =
      B.map e.toMonoidHom := by
    intro B hB
    rw [← Subgroup.map_commutator, hB]
  refine ⟨e t₁, ⟨t₁, ht₁, rfl⟩, e t₂, ⟨t₂, ht₂, rfl⟩, (hmulinv t₁).mpr h1, (hne t₁).mpr n1,
    (hmulinv t₂).mpr h2, (hne t₂).mpr n2, fun h => h12 (e.injective h),
    B₁.map e.toMonoidHom, B₂.map e.toMonoidHom, hcent _ _ hB₁, hcent _ _ hB₂, hperf _ hP₁,
    hperf _ hP₂, ?_⟩
  rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]

@[expose] def ModelData (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ (∃ t₀ : X, ∃ S₀ : Subgroup X, t₀ * t₀ = 1 ∧ t₀ ≠ 1 ∧ Layer t₀ S₀) ∧
    (∀ a b : X, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ g : X, g * a * g⁻¹ = b) ∧
    (∃ E₀ : Subgroup X, (∀ e ∈ E₀, e * e = 1) ∧ Nat.card ↥E₀ = 4 ∧ GenPair E₀)

theorem ModelData.of_mulEquiv (e : X ≃* Y) (h : ModelData X) : ModelData Y := by
  obtain ⟨hs, ⟨t₀, S₀, ht2, ht1, hS⟩, hcls, E₀, hE2, hE4, hE⟩ := h
  have _ := hs
  refine ⟨MulEquiv.isSimpleGroup e.symm, ⟨e t₀, S₀.map e.toMonoidHom, ?_, ?_, hS.map e⟩, ?_,
    E₀.map e.toMonoidHom, ?_, ?_, hE.map e⟩
  · rw [← map_mul, ht2, map_one]
  · exact (not_congr (map_eq_one_iff e e.injective)).mpr ht1
  · intro a b ha ha1 hb hb1
    obtain ⟨g, hg⟩ := hcls (e.symm a) (e.symm b) (by rw [← map_mul, ha, map_one])
      (fun h => ha1 (by simpa using congrArg e h)) (by rw [← map_mul, hb, map_one])
      (fun h => hb1 (by simpa using congrArg e h))
    refine ⟨e g, ?_⟩
    have := congrArg e hg
    simpa using this
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, hE2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hE4]

theorem locBal32_of_modelData [Finite X] (hM : ModelData X)
    (hconj : ∀ E E' : Subgroup X, (∀ e ∈ E, e * e = 1) → Nat.card ↥E = 4 → (∀ e ∈ E', e * e = 1) →
      Nat.card ↥E' = 4 → ∃ g : X, E' = E.map (MulAut.conj g).toMonoidHom)
    (B : Subgroup X) (hB : ∀ b ∈ B, b * b = 1) :
    IsLocBal32 X (B.map (MulAut.conj : X →* MulAut X)) := by
  obtain ⟨hs, ⟨t₀, S₀, ht2, ht1, hS⟩, hcls, E₀, hE2, hE4, hE⟩ := hM
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hS.quasisimple
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    refine ⟨a, b, fun h => hab' ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext h)
  have hZ : ∀ z : X, (∀ g : X, g * z = z * g) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr hz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · rw [h] at hzc
      exact hzc
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center X := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp this b).symm
  have hL : ∀ t : X, t * t = 1 → t ≠ 1 → ∃ S : Subgroup X, Layer t S := by
    intro t ht2' ht1'
    obtain ⟨g, hg⟩ := hcls t₀ t ht2 ht1 ht2' ht1'
    refine ⟨S₀.map (MulAut.conj g).toMonoidHom, ?_⟩
    have := hS.map (MulAut.conj g)
    rwa [MulAut.conj_apply, hg] at this
  have hG : ∀ E : Subgroup X, (∀ e ∈ E, e * e = 1) → Nat.card ↥E = 4 → GenPair E := by
    intro E hE2' hE4'
    obtain ⟨g, hg⟩ := hconj E₀ E hE2 hE4 hE2' hE4'
    rw [hg]
    exact hE.map (MulAut.conj g)
  exact locBal32_of_layers hZ hL hG B hB

theorem exists_four_group {A : Type} [Group A] {a b : A} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∃ E : Subgroup A, a ∈ E ∧ b ∈ E ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card ↥E = 4 := by
  have hba : b * a = a * b := hab.symm
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb2, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb2, mul_one]
  have haba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha2, one_mul]
  have habab : a * b * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b a b, hba, mul_assoc, hb2, mul_one, ha2]
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right habab
  let E : Subgroup A :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      mul_mem' := by
        intro x y hx hy
        change x = 1 ∨ x = a ∨ x = b ∨ x = a * b at hx
        change y = 1 ∨ y = a ∨ y = b ∨ y = a * b at hy
        change x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
          simp [ha2, hb2, hba, haab, hbab, habb, haba, habab]
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro x hx
        change x = 1 ∨ x = a ∨ x = b ∨ x = a * b at hx
        change x⁻¹ = 1 ∨ x⁻¹ = a ∨ x⁻¹ = b ∨ x⁻¹ = a * b
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> simp [hia, hib, hiab] }
  have hmem : ∀ x, x ∈ E ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun x => Iff.rfl
  refine ⟨E, (hmem a).2 (Or.inr (Or.inl rfl)), (hmem b).2 (Or.inr (Or.inr (Or.inl rfl))), ?_, ?_⟩
  · intro e he
    rcases (hmem e).1 he with h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact ha2
    · exact hb2
    · exact habab
  · have hset : (E : Set A) = {1, a, b, a * b} := by
      ext x
      simp only [SetLike.mem_coe, hmem, Set.mem_insert_iff, Set.mem_singleton_iff]
    have h1 : (1 : A) ≠ a := fun h => ha1 h.symm
    have h2 : (1 : A) ≠ b := fun h => hb1 h.symm
    have h3 : (1 : A) ≠ a * b := by
      intro h
      apply hne
      have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h.symm
      rw [this, hia]
    have h5 : a ≠ a * b := fun h => hb1 (left_eq_mul.mp h)
    have h6 : b ≠ a * b := fun h => ha1 (right_eq_mul.mp h)
    show Nat.card ↥(E : Set A) = 4
    rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem (by simp [h1, h2, h3]),
      Set.ncard_insert_of_notMem (by simp [hne, h5]), Set.ncard_pair h6]

theorem range_perfect {G H : Type*} [Group G] [Group H] (φ : G →* H) (hG : commutator G = ⊤) :
    ⁅φ.range, φ.range⁆ = φ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hG]

end Transport

end LocBalL3Abs

end CFSG.GH74.Generic.BProg.B3
