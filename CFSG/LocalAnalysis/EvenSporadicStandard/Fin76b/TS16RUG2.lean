module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMY
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYR0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem dihedral_conj_inv {G : Type} [Group G] {x y : G} (hyx : y * x * y⁻¹ = x⁻¹)
    {a : G} (ha : a ∈ zpowers x) : y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rw [← conj_zpow, hyx, inv_zpow]

theorem pow_four_of_mul_self_eq_one {G : Type} [Group G] {g : G} (hg : g * g = 1) :
    g ^ 4 = 1 := by
  calc g ^ 4 = (g * g) * (g * g) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [hg, one_mul]

theorem dihedral_pow_four {G : Type} [Group G] {x y : G} (hx4 : x ^ 4 = 1)
    (hy2 : y * y = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    ∀ w ∈ zpowers x ⊔ zpowers y, w ^ 4 = 1 := by
  have hA : ∀ a ∈ zpowers x, y * a * y⁻¹ ∈ zpowers x := fun a ha => by
    rw [dihedral_conj_inv hyx ha]
    exact inv_mem ha
  have hxk : ∀ k : ℤ, (x ^ k) ^ 4 = 1 := fun k => by
    have h : (x ^ k) ^ 4 = (x ^ 4) ^ k := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h, hx4, one_zpow]
  have hsq : ∀ a ∈ zpowers x, (a * y) * (a * y) = 1 := fun a ha => by
    calc a * y * (a * y) = a * (y * a * y⁻¹) * (y * y) := by group
      _ = 1 := by rw [dihedral_conj_inv hyx ha, hy2]; group
  intro w hw
  obtain ⟨a, ha, rfl | rfl⟩ := exists_mul_of_mem_sup_sigma' hy2 hA hw
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact hxk k
  · exact pow_four_of_mul_self_eq_one (hsq a ha)

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem exists_cent_64_sigma {s σ v ξ : G} (hS : S16Gen S s z t) (hD : S16LData G L z t β E σ v ξ)
    (hσs : σ * s * σ⁻¹ = s ^ 5) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ normalizer ((zpowers β : Subgroup G) : Set G) ∧
      σ ∈ R ∧ R ≤ centralizer ({σ} : Set G) ∧ (∀ r ∈ R, r ^ 4 = 1) ∧ Nat.card ↥R = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := c.hyp.outerE.cfg
  have ht2 : t * t = 1 := hcfg.t_sq
  have ht1 : t ≠ 1 := hcfg.t_ne
  have hσ2 : σ * σ = 1 := hD.σ_sq
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = zpowers (s * s) ⊔ zpowers z := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup G, F = closure ({v * v, v * ξ} : Set G) := ⟨_, rfl⟩
  have hFeq : F = E ⊓ centralizer ({σ} : Set G) := hF.trans hD.CE_eq
  have hFE : F ≤ E := by rw [hFeq]; exact inf_le_left
  have hFσ : F ≤ centralizer ({σ} : Set G) := by rw [hFeq]; exact inf_le_right
  have hFcard : Nat.card ↥F = 8 := by rw [hFeq]; exact hD.card_CE
  have hFL : F ≤ L := by
    rw [hF, closure_le]
    rintro g (rfl | rfl)
    · exact mul_mem hD.v_L hD.v_L
    · exact mul_mem hD.v_L hD.ξ_L
  have hvvF : v * v ∈ F := by
    rw [hF]; exact subset_closure (Set.mem_insert _ _)
  have hAS : A ≤ S := by
    rw [hA]
    exact sup_le (zpowers_le.2 (mul_mem hS.hs hS.hs)) (zpowers_le.2 hS.hzS)
  have hNs : zpowers (s * s) ≤ zpowers s :=
    zpowers_le.2 (mul_mem (mem_zpowers s) (mem_zpowers s))
  have hNA : zpowers (s * s) ≤ A := by rw [hA]; exact le_sup_left
  have hzA : z ∈ A := by rw [hA]; exact mem_sup_right (mem_zpowers z)
  have hAF : A ≤ centralizer (F : Set G) := fun a ha => mem_centralizer_iff.2 fun f hf =>
    mem_centralizer_iff.1 (c.SC (hAS ha)) f (hFE hf)
  have hAF' : F ≤ centralizer (A : Set G) := fun f hf => mem_centralizer_iff.2 fun a ha =>
    (mem_centralizer_iff.1 (c.SC (hAS ha)) f (hFE hf)).symm
  have hsDvd : orderOf (s * s) = 4 := by
    have h2 : (2 : ℕ) ∣ orderOf s := by rw [hS.hord]; norm_num
    rw [← pow_two, orderOf_pow_of_dvd two_ne_zero h2]
    norm_num [hS.hord]
  have hNcard : Nat.card ↥(zpowers (s * s)) = 4 := by rw [Nat.card_zpowers, hsDvd]
  have hss4 : (s * s) ^ 4 = 1 := by
    calc (s * s) ^ 4 = s ^ 8 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hS.hs8
  have hzconj : z * (s * s) * z⁻¹ = (s * s)⁻¹ := by
    calc z * (s * s) * z⁻¹ = (z * s * z⁻¹) * (z * s * z⁻¹) := by group
      _ = s⁻¹ * s⁻¹ := by rw [hS.hzs]
      _ = (s * s)⁻¹ := by group
  have hNz : ∀ a ∈ zpowers (s * s), z * a * z⁻¹ ∈ zpowers (s * s) := fun a ha => by
    rw [dihedral_conj_inv hzconj ha]
    exact inv_mem ha
  have hσs2 : σ * (s * s) * σ⁻¹ = s * s := by
    calc σ * (s * s) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * s * σ⁻¹) := by group
      _ = s ^ 5 * s ^ 5 := by rw [hσs]
      _ = s * s * s ^ 8 := by group
      _ = s * s := by rw [hS.hs8, mul_one]
  have hsσ : s * s ∈ centralizer ({σ} : Set G) :=
    mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hσs2).symm
  have hzσ : z ∈ centralizer ({σ} : Set G) := mem_centralizer_singleton_iff.2 hD.σ_z.symm
  have hAσ : A ≤ centralizer ({σ} : Set G) := by
    rw [hA]; exact sup_le (zpowers_le.2 hsσ) (zpowers_le.2 hzσ)
  have hPσ : A ⊔ F ≤ centralizer ({σ} : Set G) := sup_le hAσ hFσ
  have hβ_conj : ∀ g : G, g * β * g⁻¹ = β → g * β = β * g :=
    fun g h => mul_inv_eq_iff_eq_mul.1 h
  have hAβ : A ≤ centralizer ({β} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (c.BS β c.hyp.outerB.beta_mem a (hAS ha)).symm
  have hFβ : F ≤ centralizer ({β} : Set G) := by
    rw [hF, closure_le]
    rintro g (rfl | rfl)
    · refine mem_centralizer_singleton_iff.2 (hβ_conj _ ?_)
      calc v * v * β * (v * v)⁻¹ = v * (v * β * v⁻¹) * v⁻¹ := by group
        _ = v * β⁻¹ * v⁻¹ := by rw [hD.v_β]
        _ = (v * β * v⁻¹)⁻¹ := by group
        _ = β := by rw [hD.v_β, inv_inv]
    · refine mem_centralizer_singleton_iff.2 (hβ_conj _ ?_)
      calc v * ξ * β * (v * ξ)⁻¹ = v * (ξ * β * ξ⁻¹) * v⁻¹ := by group
        _ = v * β⁻¹ * v⁻¹ := by rw [hD.ξ_β]
        _ = (v * β * v⁻¹)⁻¹ := by group
        _ = β := by rw [hD.v_β, inv_inv]
  have hPβ : A ⊔ F ≤ centralizer ({β} : Set G) := sup_le hAβ hFβ
  have hσP : σ ∉ A ⊔ F := by
    intro hmem
    have h1 : σ * β = β * σ := mem_centralizer_singleton_iff.1 (hPβ hmem)
    have h2 : β = β⁻¹ := by
      rw [← hD.σ_β, h1]
      group
    have h3 : orderOf β ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 h2)
    rw [c.hyp.outerB.beta_order] at h3
    omega
  have hσA : ∀ a ∈ A ⊔ F, σ * a * σ⁻¹ ∈ A ⊔ F := by
    intro a ha
    have h := mem_centralizer_singleton_iff.1 (hPσ ha)
    have h' : σ * a * σ⁻¹ = a := by
      rw [← h]
      group
    rw [h']
    exact ha
  have hPzσ : A ⊔ F ≤ centralizer ((zpowers σ : Subgroup G) : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute σ a from
      (mem_centralizer_singleton_iff.1 (hPσ ha)).symm) k).eq
  have hdisj : ∀ w ∈ A ⊔ F, w ∈ zpowers σ → w = 1 := by
    intro w hw hwσ
    rcases mem_zpowers_sq_eq_one hσ2 hwσ with h | h
    · exact h
    · rw [h] at hw
      exact absurd hw hσP
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hD.σ_notL (one_mem _)
  have hσcard : Nat.card ↥(zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have htA : t ∈ A := by
    rw [hA]
    refine mem_sup_left ?_
    refine mem_zpowers_iff.2 ⟨2, ?_⟩
    rw [zpow_two]
    calc s * s * (s * s) = s ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = t := hS.hs4
  have htF : t ∈ F := by
    have h : t = (v * v) ^ 2 := by
      rw [pow_two, ← hD.v4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h]
    exact pow_mem hvvF 2
  have hint : ∀ w ∈ A, w ∈ F → w = 1 ∨ w = t := fun w hwA hwF =>
    c.hyp.wFacts.cent w (hFL hwF) fun e he => (mem_centralizer_iff.1 (c.SC (hAS hwA)) e he).symm
  have hcardA : Nat.card ↥A = 8 := by
    have hdvd16 : Nat.card ↥A ∣ 16 := by
      rw [← c.card16]
      exact Subgroup.card_dvd_of_le hAS
    have hdvd4 : 4 ∣ Nat.card ↥A := by
      rw [← hNcard]
      exact Subgroup.card_dvd_of_le hNA
    have hpos : 0 < Nat.card ↥A := Nat.card_pos
    have hne4 : Nat.card ↥A ≠ 4 := by
      intro h4
      have heq : zpowers (s * s) = A :=
        Subgroup.eq_of_le_of_card_ge hNA (by rw [hNcard, h4])
      have hzN : z ∈ zpowers (s * s) := by
        rw [heq]
        exact hzA
      exact hS.hzns (hNs hzN)
    have hne16 : Nat.card ↥A ≠ 16 := by
      intro h16
      have heq : A = S := Subgroup.eq_of_le_of_card_ge hAS (by rw [c.card16, h16])
      have hsA : s ∈ A := by
        rw [heq]
        exact hS.hs
      rw [hA] at hsA
      obtain ⟨a, ha, hsa | hsa⟩ := exists_mul_of_mem_sup_sigma' hS.hz2 hNz hsA
      · rw [← hsa] at ha
        have hc := Subgroup.card_le_of_le (zpowers_le.2 ha)
        rw [Nat.card_zpowers, Nat.card_zpowers, hS.hord, hsDvd] at hc
        omega
      · apply hS.hzns
        have hz_eq : z = a⁻¹ * s := by
          rw [hsa]
          group
        rw [hz_eq]
        exact mul_mem (inv_mem (hNs ha)) (mem_zpowers s)
    obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥A = n := ⟨_, rfl⟩
    rw [hn] at hdvd16 hdvd4 hpos hne4 hne16 ⊢
    have hle16 : n ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
    interval_cases n <;> omega
  have hcardPF : Nat.card ↥(A ⊔ F) * 2 = 8 * 8 := by
    have h := card_sup_commuting_two hAF hint ht2 ht1 htA htF
    rw [hcardA, hFcard] at h
    exact h
  have hPcard : Nat.card ↥(A ⊔ F) = 32 := by omega
  have hRcard := card_sup_commuting hPzσ hdisj
  have hRtot : Nat.card ↥((A ⊔ F) ⊔ zpowers σ) = 64 := by
    rw [hRcard, hPcard, hσcard]
  have h4A : ∀ d ∈ A, d ^ 4 = 1 := by
    rw [hA]
    exact dihedral_pow_four hss4 hS.hz2 hzconj
  have hvv4 : (v * v) ^ 4 = 1 := by
    calc (v * v) ^ 4 = v ^ 8 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hD.v8
  have hvξ2 : v * ξ * (v * ξ) = 1 := by
    calc v * ξ * (v * ξ) = (v * (ξ * v * ξ⁻¹)) * (ξ * ξ) := by group
      _ = (v * v⁻¹) * 1 := by rw [hD.ξ_v, hD.ξ_sq]
      _ = 1 := by group
  have hvξconj : v * ξ * (v * v) * (v * ξ)⁻¹ = (v * v)⁻¹ := by
    calc v * ξ * (v * v) * (v * ξ)⁻¹ = (v * (ξ * v * ξ⁻¹) * (ξ * v * ξ⁻¹)) * v⁻¹ := by
          group
      _ = (v * v⁻¹ * v⁻¹) * v⁻¹ := by rw [hD.ξ_v]
      _ = (v * v)⁻¹ := by group
  have hFsup : F ≤ zpowers (v * v) ⊔ zpowers (v * ξ) := by
    rw [hF, closure_le]
    rintro g (rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
  have h4F : ∀ f ∈ F, f ^ 4 = 1 := fun f hf =>
    dihedral_pow_four hvv4 hvξ2 hvξconj f (hFsup hf)
  have hPexp : ∀ p ∈ A ⊔ F, p ^ 4 = 1 := by
    intro p hp
    obtain ⟨d, hd, f, hf, rfl⟩ := exists_mul_of_mem_sup_comm' hAF' hp
    have hdf : Commute d f := (mem_centralizer_iff.1 (hAF hd) f hf).symm
    rw [hdf.mul_pow, h4A d hd, h4F f hf, one_mul]
  refine ⟨(A ⊔ F) ⊔ zpowers σ, IsPGroup.of_card (n := 6) (by omega), ?_,
    mem_sup_right (mem_zpowers σ), ?_, ?_, hRtot⟩
  · refine sup_le ?_ (zpowers_le.2 (mem_normalizer_zpowers_of_conj (Or.inr hD.σ_β)))
    intro a ha
    exact mem_normalizer_zpowers_of_conj (Or.inl (mul_inv_eq_iff_eq_mul.2
      (mem_centralizer_singleton_iff.1 (hPβ ha))))
  · exact sup_le hPσ (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  · intro r hr
    obtain ⟨p, hp, rfl | rfl⟩ := exists_mul_of_mem_sup_sigma' hσ2 hσA hr
    · exact hPexp _ hp
    · have hc : Commute p σ := mem_centralizer_singleton_iff.1 (hPσ hp)
      rw [hc.mul_pow, hPexp p hp, pow_four_of_mul_self_eq_one hσ2, one_mul]

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
