module

public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Transvection
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma conj_sup_mem {X Y Z : Subgroup G} {g : G} (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ Z)
    (hY : ∀ x ∈ Y, g * x * g⁻¹ ∈ Z) : ∀ x ∈ X ⊔ Y, g * x * g⁻¹ ∈ Z := by
  have h : X ⊔ Y ≤ Z.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun x hx => by simpa [MulAut.conj_apply] using hX x hx)
      (fun x hx => by simpa [MulAut.conj_apply] using hY x hx)
  intro x hx
  simpa [MulAut.conj_apply] using h hx

omit [Finite G] in
private lemma mem_normalizer_sup {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
      g ∈ Subgroup.normalizer (Y : Set G) → ∀ x ∈ X ⊔ Y, g * x * g⁻¹ ∈ X ⊔ Y := by
    intro g hX hY
    exact conj_sup_mem
      (fun x hx => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hX x).1 hx))
      (fun x hx => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hY x).1 hx))
  refine Sec7.mem_normalizer_of_conj_mem (key hX hY) (fun x hx => ?_)
  simpa using key (inv_mem hX) (inv_mem hY) x hx

omit [Finite G] in
private lemma mem_normalizer_inf {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX h, hY h]

omit [Finite G] in
private lemma mem_normalizer_centralizer {X : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (X : Set G) →
      ∀ c ∈ Subgroup.centralizer (X : Set G), g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : g⁻¹ * h * g ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hg) h).1 hh
    have e1 := Subgroup.mem_centralizer_iff.1 hc _ hh'
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [e1]
      _ = g * c * g⁻¹ * h := by group
  refine Sec7.mem_normalizer_of_conj_mem (fun x hx => key hX x hx) (fun x hx => ?_)
  simpa using key (inv_mem hX) x hx

omit [Finite G] in
private lemma conj_mem_nu {m : ℕ} {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ (⨆ (B : Subgroup G) (_ : B ≤ H ∧ IsElemAbelian 2 B ∧ 2 ^ (m - 1) ≤ Nat.card B), B :
      Subgroup G)) :
    g * x * g⁻¹ ∈ (⨆ (B : Subgroup G) (_ : B ≤ H ∧ IsElemAbelian 2 B ∧ 2 ^ (m - 1) ≤ Nat.card B),
      B : Subgroup G) := by
  have h : (⨆ (B : Subgroup G) (_ : B ≤ H ∧ IsElemAbelian 2 B ∧ 2 ^ (m - 1) ≤ Nat.card B),
      B : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      (⨆ (B : Subgroup G) (_ : B ≤ H ∧ IsElemAbelian 2 B ∧ 2 ^ (m - 1) ≤ Nat.card B), B :
      Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun B hB => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (B.map (MulAut.conj g).toMonoidHom) ⟨?_, ?_, ?_⟩ le_rfl
    · rintro _ ⟨e, he, rfl⟩
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hg e).1 (hB.1 he)
    · exact hB.2.1.map _
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hB.2.2
  simpa [MulAut.conj_apply] using h ⟨x, hx, rfl⟩

omit [Finite G] in
private lemma mem_normalizer_nu {m : ℕ} {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ (B : Subgroup G) (_ : B ≤ H ∧ IsElemAbelian 2 B ∧
      2 ^ (m - 1) ≤ Nat.card B), B : Subgroup G) : Set G) := by
  refine Sec7.mem_normalizer_of_conj_mem (fun x hx => conj_mem_nu hg hx) (fun x hx => ?_)
  simpa using conj_mem_nu (inv_mem hg) hx

omit [Finite G] in
private lemma conj_mem_omega {C : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (C : Set G))
    {x : G} (hx : x ∈ Subgroup.closure {c | c ∈ C ∧ c ^ 2 = 1}) :
    g * x * g⁻¹ ∈ Subgroup.closure {c | c ∈ C ∧ c ^ 2 = 1} := by
  have h : Subgroup.closure {c | c ∈ C ∧ c ^ 2 = 1} ≤
      (Subgroup.closure {c | c ∈ C ∧ c ^ 2 = 1}).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro c ⟨hcC, hc2⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hg c).1 hcC
    · show ((MulAut.conj g).toMonoidHom c) ^ 2 = 1
      rw [← map_pow, hc2, map_one]
  simpa [MulAut.conj_apply] using h hx

omit [Finite G] in
private lemma mem_normalizer_omega {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {c | c ∈ C ∧ c ^ 2 = 1} : Subgroup G) : Set G) := by
  refine Sec7.mem_normalizer_of_conj_mem (fun x hx => conj_mem_omega hg hx) (fun x hx => ?_)
  simpa using conj_mem_omega (inv_mem hg) hx

omit [Finite G] in
private lemma exists_pow_four_eq {P : Subgroup G} {c w : G} (hc : c ∈ P)
    (hw : w ∈ Subgroup.normalizer (P : Set G)) : ∃ p ∈ P, (c * w) ^ 4 = p * w ^ 4 := by
  have hn : ∀ n : ℕ, w ^ n * c * (w ^ n)⁻¹ ∈ P := fun n =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hw n) c).1 hc
  refine ⟨c * (w * c * w⁻¹) * (w ^ 2 * c * (w ^ 2)⁻¹) * (w ^ 3 * c * (w ^ 3)⁻¹), ?_, ?_⟩
  · have h1 := hn 1
    simp only [pow_one] at h1
    exact mul_mem (mul_mem (mul_mem hc h1) (hn 2)) (hn 3)
  · rw [pow_succ, pow_succ, pow_succ, pow_one]
    group

private lemma le_jOneOf' {S E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hcard : 2 ^ (CFSG.Open.pRank 2 S - 1) ≤ Nat.card E) : E ≤ jOneOf S :=
  le_iSup₂_of_le E ⟨hES, hE, hcard⟩ le_rfl

omit [Finite G] in
private lemma mem_centralizer_of_pow_eight {M P : Subgroup G} {y p c : G} (hP : IsPGroup 2 P)
    (hp : p ∈ P) (hPM : P ≤ Subgroup.normalizer (M : Set G))
    (hyM : y ∈ Subgroup.normalizer (M : Set G)) (hy : Odd (orderOf y))
    (hc : c ∈ Subgroup.centralizer (M : Set G)) (h8 : y ^ 8 = p * c) :
    y ∈ Subgroup.centralizer (M : Set G) := by
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  let ψ := M.normalizerMonoidHom
  let Y : Subgroup.normalizer (M : Set G) := ⟨y, hyM⟩
  let Pp : Subgroup.normalizer (M : Set G) := ⟨p, hPM hp⟩
  let Cc : Subgroup.normalizer (M : Set G) := ⟨c, Subgroup.centralizer_le_normalizer (M : Set G) hc⟩
  have hCc : ψ Cc = 1 := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hc
  have hY8 : Y ^ 8 = Pp * Cc := Subtype.ext (by simpa using h8)
  have hPk : Pp ^ 2 ^ k = 1 := Subtype.ext (by simpa using hpk)
  have hYn : Y ^ orderOf y = 1 := Subtype.ext (by simp [Y, pow_orderOf_eq_one])
  have hu8 : (ψ Y) ^ 8 = ψ Pp := by rw [← map_pow, hY8, map_mul, hCc, mul_one]
  have hu1 : (ψ Y) ^ orderOf y = 1 := by rw [← map_pow, hYn, map_one]
  have hu2 : (ψ Y) ^ 2 ^ (k + 3) = 1 := by
    have h23 : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    rw [h23, pow_mul, hu8, ← map_pow, hPk, map_one]
  have hord : orderOf (ψ Y) = 1 := by
    have hd1 : orderOf (ψ Y) ∣ orderOf y := orderOf_dvd_of_pow_eq_one hu1
    have hd2 : orderOf (ψ Y) ∣ 2 ^ (k + 3) := orderOf_dvd_of_pow_eq_one hu2
    have hcop : Nat.Coprime (orderOf y) (2 ^ (k + 3)) := (Nat.coprime_two_right.2 hy).pow_right _
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  have hψY : ψ Y = 1 := orderOf_eq_one_iff.1 hord
  have hker : Y ∈ ψ.ker := hψY
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

private lemma exists_M {S P A A₀ : Subgroup G} (hPS : P ≤ S) (hAS : A ≤ S)
    (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 2 ^ CFSG.Open.pRank 2 S) (hA₀A : A₀ ≤ A)
    (hA₀card : Nat.card A ≤ 2 * Nat.card A₀) (hZ : omegaOneZ (jOneOf S) ≤ A₀) :
    ∃ M : Subgroup G, IsElemAbelian 2 M ∧ omegaOneZ (jOneOf S) ≤ M ∧
      (∀ g ∈ Subgroup.normalizer ((P ⊔ A₀ : Subgroup G) : Set G),
        g ∈ Subgroup.normalizer (M : Set G)) ∧
      Nat.card M ≤ 2 * Nat.card (A₀ ⊓ M : Subgroup G) := by
  set m := CFSG.Open.pRank 2 S
  have hHsS : P ⊔ A₀ ≤ S := sup_le hPS (hA₀A.trans hAS)
  have hA₀card' : 2 ^ (m - 1) ≤ Nat.card A₀ := by
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.zero_sub, pow_zero]; exact hpos
    · have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hAcard, h2] at hA₀card
      omega
  set 𝔑 : Subgroup G := ⨆ (B : Subgroup G) (_ : B ≤ P ⊔ A₀ ∧ IsElemAbelian 2 B ∧
      2 ^ (m - 1) ≤ Nat.card B), B
  have hA₀𝔑 : A₀ ≤ 𝔑 := le_iSup₂_of_le A₀ ⟨le_sup_right, hA.mono hA₀A, hA₀card'⟩ le_rfl
  have h𝔑J : 𝔑 ≤ jOneOf S :=
    iSup₂_le fun B hB => le_jOneOf' (hB.1.trans hHsS) hB.2.1 hB.2.2
  set C₀ : Subgroup G := (P ⊔ A₀) ⊓ Subgroup.centralizer (𝔑 : Set G)
  have hZC₀ : omegaOneZ (jOneOf S) ≤ C₀ :=
    le_inf (hZ.trans le_sup_right)
      ((omegaOneZ_le_centralizer _).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 h𝔑J)))
  set Ω : Subgroup G := Subgroup.closure {c | c ∈ C₀ ∧ c ^ 2 = 1}
  have hΩC₀ : Ω ≤ C₀ := (Subgroup.closure_le _).2 fun c hc => hc.1
  have hΩJ : Ω ≤ jOneOf S := by
    refine (Subgroup.closure_le _).2 fun c hc => ?_
    obtain ⟨hcC, hc2⟩ := hc
    have hcomm : ∀ a ∈ A₀, ∀ b ∈ Subgroup.zpowers c, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.1 hcC.2 a (hA₀𝔑 ha)) k).eq
    have hE : IsElemAbelian 2 (A₀ ⊔ Subgroup.zpowers c) :=
      IsElemAbelian.sup_of_commute (hA.mono hA₀A) (isElemAbelian_zpowers hc2) hcomm
    have hES : A₀ ⊔ Subgroup.zpowers c ≤ S :=
      sup_le (hA₀A.trans hAS) (Subgroup.zpowers_le.2 (hHsS hcC.1))
    have hcard : 2 ^ (m - 1) ≤ Nat.card (A₀ ⊔ Subgroup.zpowers c : Subgroup G) :=
      hA₀card'.trans (Subgroup.card_le_of_le le_sup_left)
    exact le_jOneOf' hES hE hcard (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hZΩ : omegaOneZ (jOneOf S) ≤ Ω := fun z hz =>
    Subgroup.subset_closure ⟨hZC₀ hz, (isElemAbelian_omegaOneZ _).2 z hz⟩
  refine ⟨omegaOneZ Ω, isElemAbelian_omegaOneZ Ω, ?_, ?_, ?_⟩
  · intro z hz
    refine Subgroup.subset_closure ⟨?_, (isElemAbelian_omegaOneZ _).2 z hz⟩
    exact Sec7.mem_centerOf_iff'.2 ⟨hZΩ hz, fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (omegaOneZ_le_centralizer _ hz) w (hΩJ hw)).symm⟩
  · intro g hg
    have h1 : g ∈ Subgroup.normalizer (𝔑 : Set G) := mem_normalizer_nu hg
    have h2 : g ∈ Subgroup.normalizer (C₀ : Set G) :=
      mem_normalizer_inf hg (mem_normalizer_centralizer h1)
    have h3 : g ∈ Subgroup.normalizer (Ω : Set G) := mem_normalizer_omega h2
    have h4 := Sec7.normalizer_le_normalizer_tripleOf Ω 2 h3
    rwa [Sec7.tripleOf_two] at h4
  · have hMC₀ : omegaOneZ Ω ≤ C₀ := (Sec7.omegaOneZ_le Ω).trans hΩC₀
    have hc : ∀ a ∈ A₀, ∀ b ∈ omegaOneZ Ω, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hMC₀ hb).2 a (hA₀𝔑 ha)
    have hEZ : IsElemAbelian 2 (A₀ ⊔ omegaOneZ Ω) :=
      IsElemAbelian.sup_of_commute (hA.mono hA₀A) (isElemAbelian_omegaOneZ Ω) hc
    have hle : A₀ ⊔ omegaOneZ Ω ≤ S :=
      sup_le (hA₀A.trans hAS) ((hMC₀.trans inf_le_left).trans hHsS)
    obtain ⟨k, hk⟩ := hEZ.isPGroup.exists_card_eq
    have hkm : k ≤ m := CFSG.SectionRank.le_pRank Nat.one_lt_two hle hEZ hk
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀ (omegaOneZ Ω) hc).1
    rw [hk] at hprod
    have h2k : 2 ^ k ≤ 2 * Nat.card A₀ :=
      calc 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hkm
        _ = Nat.card A := hAcard.symm
        _ ≤ 2 * Nat.card A₀ := hA₀card
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card A₀ * Nat.card (omegaOneZ Ω)
        = 2 ^ k * Nat.card (A₀ ⊓ omegaOneZ Ω : Subgroup G) := hprod.symm
      _ ≤ 2 * Nat.card A₀ * Nat.card (A₀ ⊓ omegaOneZ Ω : Subgroup G) := Nat.mul_le_mul_right _ h2k
      _ = Nat.card A₀ * (2 * Nat.card (A₀ ⊓ omegaOneZ Ω : Subgroup G)) := by ring

theorem centralizer_omegaOneZ_jOneOf {S P A A₀ : Subgroup G} {y e : G}
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hAS : A ≤ S) (hA : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ pRank 2 S) (hA₀A : A₀ ≤ A) (hA₀card : Nat.card A ≤ 2 * Nat.card A₀)
    (hy : Odd (orderOf y)) (heA : e ∈ A)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hyP : y ∈ Subgroup.normalizer (P : Set G))
    (hinv : e * y * e⁻¹ * y ∈ P) (hA₀y : ∀ a ∈ A₀, a * y * a⁻¹ * y⁻¹ ∈ P)
    (hZ : omegaOneZ (jOneOf S) ≤ A₀)
    (h3 : ∀ g ∈ Subgroup.closure ((A : Set G) ∪ {y}), ¬ 3 ∣ orderOf g) :
    y ∈ Subgroup.centralizer (omegaOneZ (jOneOf S) : Set G) := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hAcard
  have hAHs : A ≤ Subgroup.normalizer ((P ⊔ A₀ : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_sup (hAP ha) (Sec7.mem_normalizer_of_conj_mem (fun x hx => ?_)
      (fun x hx => ?_))
    · rw [hA.comm ha (hA₀A hx), mul_assoc, mul_inv_cancel, mul_one]; exact hx
    · rw [hA.comm (inv_mem ha) (hA₀A hx), mul_assoc, inv_mul_cancel, mul_one]; exact hx
  have hPHs : P ≤ Subgroup.normalizer ((P ⊔ A₀ : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hyHs : y ∈ Subgroup.normalizer ((P ⊔ A₀ : Subgroup G) : Set G) := by
    have hyP' : y⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hyP
    refine Sec7.mem_normalizer_of_conj_mem (conj_sup_mem (fun x hx => ?_) (fun a ha => ?_))
      (fun x hx => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hyP x).1 hx)
    · have hp := hA₀y a⁻¹ (inv_mem ha)
      have h : y * a * y⁻¹ = a * (a⁻¹ * y * a⁻¹⁻¹ * y⁻¹) := by group
      rw [h]
      exact mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hp)
    · have key := conj_sup_mem (g := y⁻¹) (X := P) (Y := A₀) (Z := P ⊔ A₀)
        (fun x hx => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hyP' x).1 hx))
        (fun a ha => by
          have hp := (Subgroup.mem_normalizer_iff.1 hyP' _).1 (hA₀y a ha)
          have h : y⁻¹ * a * y⁻¹⁻¹ = (y⁻¹ * (a * y * a⁻¹ * y⁻¹) * y⁻¹⁻¹) * a := by group
          rw [h]
          exact mul_mem (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ha)) x hx
      simpa using key
  obtain ⟨M, hM, hZM, hMn, hMcard⟩ := exists_M hPS hAS hA hAcard hA₀A hA₀card hZ
  have heM : e ∈ Subgroup.normalizer (M : Set G) := hMn e (hAHs heA)
  have hyM : y ∈ Subgroup.normalizer (M : Set G) := hMn y hyHs
  have hPM : P ≤ Subgroup.normalizer (M : Set G) := fun p hp => hMn p (hPHs hp)
  have hce : Nat.card M ≤ 2 * Nat.card (M ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) := by
    refine hMcard.trans (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le ?_))
    intro x hx
    exact ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.2 (hA.comm (hA₀A hx.1) heA)⟩
  have hfM : y⁻¹ * e * y ∈ Subgroup.normalizer (M : Set G) :=
    mul_mem (mul_mem (inv_mem hyM) heM) hyM
  have hcf : Nat.card M ≤
      2 * Nat.card (M ⊓ Subgroup.centralizer ({y⁻¹ * e * y} : Set G) : Subgroup G) := by
    refine hce.trans (Nat.mul_le_mul_left 2 ?_)
    have hle : (M ⊓ Subgroup.centralizer ({e} : Set G)).map (MulAut.conj y⁻¹).toMonoidHom ≤
        M ⊓ Subgroup.centralizer ({y⁻¹ * e * y} : Set G) := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 (inv_mem hyM) w).1 hw.1
      · have hwe := Subgroup.mem_centralizer_singleton_iff.1 hw.2
        show y⁻¹ * w * y⁻¹⁻¹ * (y⁻¹ * e * y) = y⁻¹ * e * y * (y⁻¹ * w * y⁻¹⁻¹)
        calc y⁻¹ * w * y⁻¹⁻¹ * (y⁻¹ * e * y) = y⁻¹ * (w * e) * y := by group
          _ = y⁻¹ * (e * w) * y := by rw [hwe]
          _ = y⁻¹ * e * y * (y⁻¹ * w * y⁻¹⁻¹) := by group
    calc Nat.card (M ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G)
        = Nat.card ((M ⊓ Subgroup.centralizer ({e} : Set G)).map (MulAut.conj y⁻¹).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have h3' : ¬ 3 ∣ orderOf (e * (y⁻¹ * e * y)) := by
    refine h3 _ ?_
    have hyc : y ∈ Subgroup.closure ((A : Set G) ∪ {y}) := Subgroup.subset_closure (Or.inr rfl)
    have hec : e ∈ Subgroup.closure ((A : Set G) ∪ {y}) := Subgroup.subset_closure (Or.inl heA)
    exact mul_mem hec (mul_mem (mul_mem (inv_mem hyc) hec) hyc)
  have h4 := pow_four_mem_centralizer hM heM hfM hce hcf h3'
  have he_inv : e⁻¹ = e := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hA.2 e heA
  have hq : y * (e * y * e⁻¹ * y)⁻¹ * y⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.1 hyP _).1 (inv_mem hinv)
  have hef : e * (y⁻¹ * e * y) = (y * (e * y * e⁻¹ * y)⁻¹ * y⁻¹) * y ^ 2 :=
    calc e * (y⁻¹ * e * y) = e * y⁻¹ * e⁻¹ * y := by rw [he_inv]; group
      _ = (y * (e * y * e⁻¹ * y)⁻¹ * y⁻¹) * y ^ 2 := by group
  obtain ⟨p₁, hp₁, h4eq⟩ := exists_pow_four_eq hq (Subgroup.pow_mem _ hyP 2)
  rw [← hef] at h4eq
  have h8 : y ^ 8 = p₁⁻¹ * (e * (y⁻¹ * e * y)) ^ 4 := by
    rw [h4eq, ← mul_assoc, inv_mul_cancel, one_mul, ← pow_mul]
  have hyc : y ∈ Subgroup.centralizer (M : Set G) :=
    mem_centralizer_of_pow_eight (hS.to_le hPS) (inv_mem hp₁) hPM hyM hy h4 h8
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hZM) hyc

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
