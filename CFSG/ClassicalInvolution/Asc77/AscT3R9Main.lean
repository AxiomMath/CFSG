module

public import CFSG.ClassicalInvolution.Asc77.AscT3RStd
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9Main
public import CFSG.ClassicalInvolution.Asc77.AscT3RFAut
public import CFSG.ClassicalInvolution.Asc77.AscT3RInv

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Conj

variable {G : Type} [Group G]

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem InducesFAut.conj [Finite G] {K R : Subgroup G} {a : G} (h : InducesFAut K R a) (g : G) :
    InducesFAut (conjSub g K) (conjSub g R) (g * a * g⁻¹) := by
  obtain ⟨haN, ha2, P, hP, hq, hc⟩ := h
  refine ⟨?_, ?_, conjSub g P, ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq] at haN ⊢
    rw [← conjSub_mul]
    have e : g * a * g⁻¹ * g = g * a := by group
    rw [e, conjSub_mul, haN]
  · have h1 := late_cmo_conj_mem ha2 g
    rw [conjSub_top] at h1
    have e : g * (a * a) * g⁻¹ = g * a * g⁻¹ * (g * a * g⁻¹) := by group
    rw [e] at h1
    exact h1
  · have h1 := IsSylow2In.conj hP g
    rwa [late_conjSub_inf, Balance.conjSub_centralizer_singleton] at h1
  · obtain ⟨k, hk, ⟨e⟩⟩ := hq
    refine ⟨k, hk, ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e
  · rw [late_natCard_conjSub, late_natCard_conjSub]
    exact hc

end Conj


section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



theorem Std20.r9_aux (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (h3 : ∀ u ∈ (S : Subgroup G), u * u ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      u ∈ Subgroup.normalizer (K : Set G)) :
    (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
      x * x ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      y * y ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' →
        x ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
        y ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
        x * y ∈ sec20X (CoreAssembly.conjClass K) z K K') ∧
    (∃ (eK : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f)) (u a₂ : G)
      (γ γ' : MulAut SL(2, GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f),
      u ∈ (S : Subgroup G) ∧ conjSub u K = K' ∧ a₂ ∈ (S : Subgroup G) ∧
      a₂ ∉ sec20X (CoreAssembly.conjClass K) z K K' ∧
      a₂ ∈ Subgroup.normalizer (K : Set G) ∧
      u⁻¹ * a₂ * u ∈ Subgroup.normalizer (K : Set G) ∧ σ * σ = 1 ∧ σ ≠ 1 ∧
      phiG K eK a₂ = γ * slFieldAut (GaloisField p f) σ * γ⁻¹ ∧
      phiG K eK (u⁻¹ * a₂ * u) = γ' * slFieldAut (GaloisField p f) σ * γ'⁻¹ ∧
      (∃ n : ℕ, a₂ ^ (2 ^ n) = 1) ∧ (∃ n : ℕ, (u⁻¹ * a₂ * u) ^ (2 ^ n) = 1)) := by
  classical
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hKop : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.one_le_iff_ne_zero.mpr hf, hFcard⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hFcard]
    omega
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.late_mem_K
  obtain ⟨eK⟩ := hz₀.nonempty_equiv
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  have hK'u := d.late_swap_data hu huK
  obtain ⟨v, hv, hord, hvN⟩ := d.r9_vdata
  obtain ⟨hεv, hρv⟩ := d.r9_eps_v c8 hu huK eK hFodd hKop h4 hv hord hvN
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.to_le inf_le_left
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hRT : R ≤ T := le_inf d.hRS (d.hR.1.trans Subgroup.le_normalizer)
  have hR'T : R' ≤ T := le_inf d.hR'S (d.hR'.1.trans d.late_K'_le)
  have hVT : V ≤ T := le_inf d.hVS (d.hVW.trans d.late_W_le_N_K)
  have hvT : v ∈ T := hVT hvV
  have hTR : ∀ x ∈ T, x ∈ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [d.late_R_eq]
    exact late_mem_normalizer_inf hx.2 (Subgroup.le_normalizer hx.1)
  have hRp : ∀ y ∈ T, phiG K eK y = 1 → y ∈ R' := fun y hyT hy1 =>
    d.r9_cStar_S c8 hu huK hyT.1 ((phiG_eq_one_iff hyT.2).mp hy1)
  have hRp' : ∀ y ∈ R', phiG K eK y = 1 := fun y hy =>
    (phiG_eq_one_iff (hTN (hR'T hy))).mpr (d.r9_K'_le_cStar (d.hR'.1 hy))
  have hRR'V_le_X : R ⊔ R' ⊔ V ≤ X :=
    sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX
  have hψker : ∀ x ∈ T, psi hKop K eK v x = 1 → x ∈ X := fun x hxT hψ =>
    hRR'V_le_X (mem_of_psi_eq_one hFodd h4 hT2 hTN hRT d.hR hRp hvV hvT hεv hxT hψ)
  have hψone : ∀ x ∈ (S : Subgroup G) ⊓ X, psi hKop K eK v x = 1 := by
    intro x hx
    have hx' : x ∈ R ⊔ R' ⊔ V := (d.late_SX c3).symm ▸ hx
    exact psi_eq_one_of_mem hρv hεv hTN d.hR.1 hRT hR'T hRp' hvT hv hx'
  have hA : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * x ∈ X → y * y ∈ X → ⁅x, y⁆ ∈ X →
      x ∈ X ∨ y ∈ X ∨ x * y ∈ X := by
    intro x hx y hy hx2 hy2 _
    by_contra hcon
    push Not at hcon
    obtain ⟨hxX, hyX, hxyX⟩ := hcon
    have hxN := h3 x hx hx2
    have hyN := h3 y hy hy2
    have hxT : x ∈ T := ⟨hx, hxN⟩
    have hyT : y ∈ T := ⟨hy, hyN⟩
    have hψx : psi hKop K eK v x ≠ 1 := fun h => hxX (hψker x hxT h)
    have hψy : psi hKop K eK v y ≠ 1 := fun h => hyX (hψker y hyT h)
    have hψx2 : psi hKop K eK v x * psi hKop K eK v x = 1 := by
      rw [← psi_mul hρv hxN hxN]
      exact hψone _ ⟨S.mul_mem hx hx, hx2⟩
    have hψy2 : psi hKop K eK v y * psi hKop K eK v y = 1 := by
      rw [← psi_mul hρv hyN hyN]
      exact hψone _ ⟨S.mul_mem hy hy, hy2⟩
    exact hxyX (hψker (x * y) (T.mul_mem hxT hyT)
      (psi_mul_eq_one hρv hxN hyN hψx hψy hψx2 hψy2))
  refine ⟨hA, ?_⟩
  have hex : ∃ n : ℕ, u ^ (2 ^ n) ∈ X := by
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨u, hu⟩
    have h1 : u ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, by rw [h1]; exact X.one_mem⟩
  have hunotN : u ∉ Subgroup.normalizer (K : Set G) := fun h =>
    d.ne (huK.symm.trans (mem_normalizer_iff_conjSub_eq.mp h))
  have hu2N : u * u ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, huK, hK'u.1]
  have hu_notX : u ∉ X := fun h => hunotN (h3 u hu (X.mul_mem h h))
  have hu2_notX : u * u ∉ X := fun h => hunotN (h3 u hu h)
  set n₀ := Nat.find hex with hn₀
  have hspec : u ^ (2 ^ n₀) ∈ X := Nat.find_spec hex
  have hmin : ∀ m < n₀, u ^ (2 ^ m) ∉ X := fun m hm => Nat.find_min hex hm
  have hn2 : 2 ≤ n₀ := by
    by_contra hlt
    have : n₀ = 0 ∨ n₀ = 1 := by omega
    rcases this with h | h
    · rw [h] at hspec
      exact hu_notX (by simpa using hspec)
    · rw [h] at hspec
      exact hu2_notX (by simpa [pow_two] using hspec)
  set a : G := u ^ (2 ^ (n₀ - 1)) with ha
  have haX : a ∉ X := hmin (n₀ - 1) (by omega)
  have ha2X : a * a ∈ X := by
    have : a * a = u ^ (2 ^ n₀) := by
      rw [ha, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [this]
    exact hspec
  have haS : a ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem hu _
  have haN : a ∈ Subgroup.normalizer (K : Set G) := by
    have : a = (u * u) ^ (2 ^ (n₀ - 2)) := by
      rw [ha, ← pow_two, ← pow_mul, ← pow_succ']
      congr 2
      omega
    rw [this]
    exact Subgroup.pow_mem _ hu2N _
  have hau : a * u = u * a := by
    rw [ha]
    exact ((Commute.refl u).pow_left _).eq
  have hau' : u⁻¹ * a * u = a := by
    calc u⁻¹ * a * u = u⁻¹ * (a * u) := by group
      _ = a := by rw [hau]; group
  have haT : a ∈ T := ⟨haS, haN⟩
  have hψa : psi hKop K eK v a ≠ 1 := fun h => haX (hψker a haT h)
  have hψa2 : psi hKop K eK v a * psi hKop K eK v a = 1 := by
    rw [← psi_mul hρv haN haN]
    exact hψone _ ⟨S.mul_mem haS haS, ha2X⟩
  set w : G := u⁻¹ * v * u with hw
  have hwS : w ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem (S.inv_mem hu) (d.hVS hvV)) hu
  have hwX : w ∈ X := by
    have h1 : conjSub u⁻¹ X ≤ X := conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins
      (Subgroup.inv_mem _ (d.hSz hu))
    have h2 : w ∈ conjSub u⁻¹ X := by
      rw [mem_conjSub_iff]
      have e : (u⁻¹)⁻¹ * w * u⁻¹ = v := by rw [hw]; group
      rw [e]
      exact tw.hVX hvV
    exact h1 h2
  have hwN : w ∈ Subgroup.normalizer (K : Set G) := h3 w hwS (X.mul_mem hwX hwX)
  have hwT : w ∈ T := ⟨hwS, hwN⟩
  have hwψ : psi hKop K eK v w = 1 := hψone w ⟨hwS, hwX⟩
  have hεw : epsG hKop K eK w ≠ 1 := by
    intro hε1
    have hρ1 : rhoG K eK w = 1 := by simpa [psi, hε1] using hwψ
    have hwRR' := mem_of_inner_action hFodd h4 hT2 hTN hRT d.hR hRp hwT hε1 hρ1
    have hvRR' : v ∈ R' ⊔ R := by
      have h1 : u * w * u⁻¹ ∈ conjSub u (R ⊔ R') := ⟨w, hwRR', rfl⟩
      rw [late_conjSub_sup, hK'u.2.1] at h1
      have h2 : conjSub u R' = R := by
        rw [d.late_R'_eq, late_conjSub_inf, hK'u.1, hK'u.2.2.2, d.late_R_eq]
      rw [h2] at h1
      have e : u * w * u⁻¹ = v := by rw [hw]; group
      rwa [e] at h1
    have : epsG hKop K eK v = 1 := by
      refine epsG_eq_one_of_mem_sup (R₁ := R') (R₂ := R) ?_ ?_ hvRR'
      · exact fun x hx => ⟨hTN (hR'T hx), epsG_of_phiG_eq_one (hRp' x hx)⟩
      · exact fun x hx => ⟨Subgroup.le_normalizer (d.hR.1 hx), epsG_of_mem_L (d.hR.1 hx)⟩
    exact hεv this
  have hρw : rhoG K eK w = rhoG K eK v := by
    have h1 : rhoG K eK w * rhoG K eK v = 1 := by simpa [psi, hεw] using hwψ
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (eq_inv_of_mul_eq_one_left hρv).symm
  have hclaim : ∃ a₀ ∈ T, a₀ ∉ X ∧ epsG hKop K eK a₀ = 1 ∧
      rhoG K eK a₀ = psi hKop K eK v a ∧
      u⁻¹ * a₀ * u ∈ T ∧ epsG hKop K eK (u⁻¹ * a₀ * u) = 1 ∧
      rhoG K eK (u⁻¹ * a₀ * u) = psi hKop K eK v a := by
    by_cases hεa : epsG hKop K eK a = 1
    · refine ⟨a, haT, haX, hεa, by simp [psi, hεa], by rw [hau']; exact haT,
        by rw [hau']; exact hεa, by rw [hau']; simp [psi, hεa]⟩
    · have hψa' : psi hKop K eK v a = rhoG K eK a * rhoG K eK v := by simp [psi, hεa]
      have hconj : u⁻¹ * (a * v) * u = a * w := by
        calc u⁻¹ * (a * v) * u = (u⁻¹ * a * u) * (u⁻¹ * v * u) := by group
          _ = a * w := by rw [hau']
      refine ⟨a * v, T.mul_mem haT hvT, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hav
        apply haX
        have := X.mul_mem hav (X.inv_mem (tw.hVX hvV))
        simpa using this
      · rw [epsG_mul haN hvN]
        exact z2_mul_of_ne_one hεa hεv
      · rw [rhoG_mul haN hvN, hψa']
      · rw [hconj]
        exact T.mul_mem haT hwT
      · rw [hconj, epsG_mul haN hwN]
        exact z2_mul_of_ne_one hεa hεw
      · rw [hconj, rhoG_mul haN hwN, hρw, hψa']
  obtain ⟨a₀, ha₀T, ha₀X, hε₀, hρ₀, hb₀T, hεb₀, hρb₀⟩ := hclaim
  obtain ⟨r, hr, γ, hγ⟩ := exists_field_involution_mul hFodd hKop h4 hT2 hTN hRT d.hR hTR
    hψa2 hψa ha₀T hε₀ hρ₀
  obtain ⟨r₂, hr₂, γ', hγ'⟩ := exists_field_involution_mul hFodd hKop h4 hT2 hTN hRT d.hR hTR
    hψa2 hψa hb₀T hεb₀ hρb₀
  have hR'conj : conjSub u R' = R := by
    rw [d.late_R'_eq, late_conjSub_inf, hK'u.1, hK'u.2.2.2, d.late_R_eq]
  have hr'R' : u * r₂ * u⁻¹ ∈ R' := by
    have h1 : u * r₂ * u⁻¹ ∈ conjSub u R := ⟨r₂, hr₂, rfl⟩
    rwa [hK'u.2.1] at h1
  have hr₁R' : u⁻¹ * r * u ∈ R' := by
    have h1 : u⁻¹ * r * u ∈ conjSub u⁻¹ R := by
      rw [mem_conjSub_iff]
      have e : (u⁻¹)⁻¹ * (u⁻¹ * r * u) * u⁻¹ = r := by group
      rw [e]
      exact hr
    have h2 : conjSub u⁻¹ R = R' := by rw [← hR'conj, conjSub_inv_conjSub]
    rwa [h2] at h1
  have hNa₀ := hTN ha₀T
  have hNr := hTN (hRT hr)
  have hNr₂ := hTN (hRT hr₂)
  have hNr' := hTN (hR'T hr'R')
  have hNr₁ := hTN (hR'T hr₁R')
  have hNb₀ := hTN hb₀T
  set a₂ : G := a₀ * r * (u * r₂ * u⁻¹) with ha₂
  have ha₂T : a₂ ∈ T := T.mul_mem (T.mul_mem ha₀T (hRT hr)) (hR'T hr'R')
  have hNa₂ := hTN ha₂T
  have hphi₁ : phiG K eK a₂ = γ * slFieldAut (GaloisField p f) (psi hKop K eK v a) * γ⁻¹ := by
    rw [ha₂, phiG_mul (Subgroup.mul_mem _ hNa₀ hNr) hNr', hRp' _ hr'R', mul_one,
      phiG_mul hNa₀ hNr]
    rw [phiG_mul hNa₀ hNr] at hγ
    exact hγ
  set b₂ : G := u⁻¹ * a₂ * u with hb₂
  have hb₂eq : b₂ = (u⁻¹ * a₀ * u) * (u⁻¹ * r * u) * r₂ := by
    rw [hb₂, ha₂]
    group
  have hNb₂ : b₂ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hb₂eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hNb₀ hNr₁) hNr₂
  have hphi₂ : phiG K eK b₂ = γ' * slFieldAut (GaloisField p f) (psi hKop K eK v a) * γ'⁻¹ := by
    rw [hb₂eq, phiG_mul (Subgroup.mul_mem _ hNb₀ hNr₁) hNr₂, phiG_mul hNb₀ hNr₁,
      hRp' _ hr₁R', mul_one, ← phiG_mul hNb₀ hNr₂]
    exact hγ'
  have hσ1 : psi hKop K eK v a ≠ 1 := hψa
  have hσ2 : psi hKop K eK v a * psi hKop K eK v a = 1 := hψa2
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, a₂ ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨a₂, ha₂T.1⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hb₂S : b₂ ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem (S.inv_mem hu) ha₂T.1) hu
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, b₂ ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨b₂, hb₂S⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have ha₂X : a₂ ∉ X := by
    intro h
    apply ha₀X
    have hrX : r ∈ X := hRR'V_le_X (Subgroup.mem_sup_left (Subgroup.mem_sup_left hr))
    have hr'X : u * r₂ * u⁻¹ ∈ X :=
      hRR'V_le_X (Subgroup.mem_sup_left (Subgroup.mem_sup_right hr'R'))
    have := X.mul_mem (X.mul_mem h (X.inv_mem hr'X)) (X.inv_mem hrX)
    have e : a₀ = a₂ * (u * r₂ * u⁻¹)⁻¹ * r⁻¹ := by
      rw [ha₂]
      group
    rw [e]
    exact this
  exact ⟨eK, u, a₂, γ, γ', psi hKop K eK v a, hu, huK, ha₂T.1, ha₂X, hNa₂, hNb₂, hσ2, hσ1,
    hphi₁, hphi₂, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩

theorem Std20.r9_main (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (h3 : ∀ u ∈ (S : Subgroup G), u * u ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      u ∈ Subgroup.normalizer (K : Set G)) :
    (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
      x * x ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      y * y ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' →
        x ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
        y ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
        x * y ∈ sec20X (CoreAssembly.conjClass K) z K K') ∧
    (∃ a ∈ (S : Subgroup G), InducesFAut K R a ∧ InducesFAut K' R' a) := by
  classical
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  obtain ⟨hA, eK, u, a₂, γ, γ', σ, hu, huK, ha₂S, -, hNa₂, hNb₂, hσ2, hσ1, hphi₁, hphi₂,
    ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ := d.r9_aux c3 c8 h3
  refine ⟨hA, a₂, ha₂S, ?_⟩
  have hK'u := d.late_swap_data hu huK
  obtain ⟨hsq₁, P₁, hP₁, hq₁, hc₁⟩ := field_involution_data hFodd hσ2 hσ1 hNa₂ hn₁ hphi₁ d.hR
  obtain ⟨hsq₂, P₂, hP₂, hq₂, hc₂⟩ := field_involution_data hFodd hσ2 hσ1 hNb₂ hn₂ hphi₂ d.hR
  have hFA₁ : InducesFAut K R a₂ :=
    ⟨hNa₂, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₁, P₁, hP₁, hq₁, hc₁⟩
  have hFA₂ : InducesFAut K R (u⁻¹ * a₂ * u) :=
    ⟨hNb₂, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₂, P₂, hP₂, hq₂, hc₂⟩
  have hFA₂' := hFA₂.conj u
  have e : u * (u⁻¹ * a₂ * u) * u⁻¹ = a₂ := by group
  rw [huK, hK'u.2.1, e] at hFA₂'
  exact ⟨hFA₁, hFA₂'⟩

end Main

section Final

variable (p f : ℕ) [Fact p.Prime]



theorem c20_9rest : C20_9Rest p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 h8 h3
  exact d.r9_main c3 c8 h3

end Final


end CFSG.ClassicalInvolution.Asc77.T3CII
