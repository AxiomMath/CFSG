module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFusion

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup

section Transfer

variable {G : Type*} [Group G]

private theorem inv_mul_mul_pow' (g x : G) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

variable [Finite G]

theorem exists_normal_index_two_of_forall_inner_of_odd_of_le {L M₀ : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hLM : L ≤ M₀) (htM : t ∈ M₀) (hM : M₀ ≤ centralizer ({t} : Set G))
    (hMN : M₀ ≤ normalizer (L : Set G))
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hA : ∀ g : G, g⁻¹ * t * g ∈ M₀ → t * (g⁻¹ * t * g) ∈ L)
    {x₀ : G} (hx₀ : x₀ ∈ M₀)
    (hgen : M₀ ≤ L ⊔ zpowers x₀ ⊔ zpowers t)
    (hlift : ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t)
    (hodd : ¬ 2 ∣ M₀.index) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := M₀
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htL : t ∉ L := by simpa using hnot 1
  have : (L.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hLM).2 hMN
  set π := QuotientGroup.mk' (L.subgroupOf M) with hπdef
  have hπeq : ∀ g h (hg : g ∈ M) (hh : h ∈ M), π ⟨g, hg⟩ = π ⟨h, hh⟩ ↔ g⁻¹ * h ∈ L :=
    fun g h hg hh => by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        mem_subgroupOf]
      rfl
  have hπ1 : ∀ g (hg : g ∈ M), π ⟨g, hg⟩ = 1 ↔ g ∈ L := fun g hg => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hπpow : ∀ g (hg : g ∈ M) (n : ℕ), π ⟨g, hg⟩ ^ n = π ⟨g ^ n, pow_mem hg n⟩ :=
    fun g hg n => by rw [← map_pow]; rfl
  have hπmul : ∀ g h (hg : g ∈ M) (hh : h ∈ M),
      π ⟨g, hg⟩ * π ⟨h, hh⟩ = π ⟨g * h, mul_mem hg hh⟩ :=
    fun g h hg hh => by rw [← map_mul]; rfl
  have hx0L : ∀ n : ℕ, x₀ ^ n ∈ L → x₀ ^ n = 1 := fun n hn => by
    rcases F4Pilot.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht (hlift n (mem_sup_left hn))
      with h | h
    · exact h
    · exact absurd (h ▸ hn) htL
  set w := π ⟨x₀, hx₀⟩ with hwdef
  have hw : orderOf w = orderOf x₀ := orderOf_eq_orderOf_iff.2 fun n => by
    rw [hwdef, hπpow, hπ1]
    exact ⟨hx0L n, fun h => h ▸ L.one_mem⟩
  set K := ((zpowers w).comap π).map M.subtype
  have hmemK : ∀ g (hg : g ∈ M), g ∈ K ↔ π ⟨g, hg⟩ ∈ zpowers w := fun g hg =>
    (mem_map_iff_mem M.subtype_injective (x := ⟨g, hg⟩)).trans mem_comap
  have hLK : L ⊔ zpowers x₀ ≤ K := sup_le
    (fun l hl => (hmemK l (hLM hl)).2 (by rw [(hπ1 l (hLM hl)).2 hl]; exact one_mem _))
    (zpowers_le.2 ((hmemK x₀ hx₀).2 (mem_zpowers w)))
  have hpowK : ∀ g (hg : g ∈ M), g ∈ K → ∃ k : ℕ, π ⟨g, hg⟩ = w ^ k := fun g hg hgK => by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_iff_mem_zpowers.2 ((hmemK g hg).1 hgK))
    exact ⟨k, hk.symm⟩
  by_cases htx : t ∈ zpowers x₀
  ·
    have hMK : M ≤ K := hgen.trans (sup_le hLK (zpowers_le.2 (hLK (mem_sup_right htx))))
    have hQ : ∀ g (hg : g ∈ M), ∃ k : ℕ, π ⟨g, hg⟩ = w ^ k := fun g hg => hpowK g hg (hMK hg)
    obtain ⟨c, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
    have h2x : 2 ∣ orderOf x₀ := ht ▸ orderOf_dvd_of_mem_zpowers htx
    obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := by
      rcases c with _ | b
      · rw [hcm, pow_zero, one_mul] at h2x
        exact absurd (even_iff_two_dvd.2 h2x) (Nat.not_even_iff_odd.2 hm)
      · exact ⟨b, rfl⟩
    have hw2 : orderOf w = 2 ^ (b + 1) * m := hw.trans hcm
    have hpar : ∀ k : ℕ, w ^ k ∈ zpowers (w ^ 2) ↔ Even k := fun k => by
      constructor
      · intro hk
        obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hk)
        rw [← pow_mul] at hj
        have h1 := pow_eq_pow_iff_modEq.1 hj
        rw [hw2] at h1
        have h3 : 2 * j ≡ k [MOD 2] :=
          Nat.ModEq.of_dvd (dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.succ_ne_zero b)) m) h1
        unfold Nat.ModEq at h3
        exact Nat.even_iff.2 (by omega)
      · rintro ⟨j, rfl⟩
        rw [← two_mul, pow_mul]
        exact pow_mem (mem_zpowers _) j
    set Y := ((zpowers (w ^ 2)).comap π).map M.subtype
    have hYM : Y ≤ M := map_subtype_le _
    have hmemY : ∀ g (hg : g ∈ M), g ∈ Y ↔ π ⟨g, hg⟩ ∈ zpowers (w ^ 2) := fun g hg =>
      (mem_map_iff_mem M.subtype_injective (x := ⟨g, hg⟩)).trans mem_comap
    have hYidx : Y.relIndex M = 2 := by
      rw [relIndex_eq_two_iff_exists_notMem_and]
      refine ⟨x₀, hx₀, fun h => Nat.not_even_one ((hpar 1).1 ?_), fun g hg => ?_⟩
      · rw [pow_one]
        exact (hmemY x₀ hx₀).1 h
      · obtain ⟨k, hk⟩ := hQ g hg
        rcases Nat.even_or_odd k with hke | hko
        · exact Or.inr ((hmemY g hg).2 (by rw [hk]; exact (hpar k).2 hke))
        · refine Or.inl ((hmemY _ (mul_mem hg hx₀)).2 ?_)
          rw [← hπmul g x₀ hg hx₀, hk, ← hwdef, ← pow_succ]
          exact (hpar _).2 hko.add_one
    have hxM : x₀ ^ m ∈ M := pow_mem hx₀ m
    have hxo : orderOf (x₀ ^ m) = 2 ^ (b + 1) := by
      rw [orderOf_pow_of_dvd hm.pos.ne' (hcm ▸ dvd_mul_left m _), hcm,
        Nat.mul_div_cancel _ hm.pos]
    have hxY : x₀ ^ m ∉ Y := by
      rw [hmemY _ hxM, ← hπpow x₀ hx₀ m, ← hwdef, hpar]
      exact Nat.not_even_iff_odd.2 hm
    have hmin : ∀ y ∈ M, y ∉ Y → IsPGroup 2 (zpowers y) → orderOf (x₀ ^ m) ≤ orderOf y := by
      intro y hy hyY _
      obtain ⟨k, hk⟩ := hQ y hy
      have hko : Odd k := Nat.not_even_iff_odd.1 fun he =>
        hyY ((hmemY y hy).2 (by rw [hk]; exact (hpar k).2 he))
      have h1 : w ^ (k * orderOf y) = 1 := by
        rw [pow_mul, ← hk, hπpow, hπ1, pow_orderOf_eq_one]
        exact one_mem L
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hw2] at h2
      have h3 : 2 ^ (b + 1) ∣ orderOf y :=
        (Nat.Coprime.pow_left (b + 1) (Nat.coprime_two_left.2 hko)).dvd_of_dvd_mul_left
          ((dvd_mul_right _ m).trans h2)
      rw [hxo]
      exact Nat.le_of_dvd (orderOf_pos y) h3
    obtain ⟨k₁, hk₁⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 htx)
    have hdiv : 2 ^ b * m ∣ k₁ := by
      have h1 : x₀ ^ (2 * k₁) = 1 := by rw [pow_mul', hk₁, sq, htt]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hcm, pow_succ', mul_assoc] at h2
      exact (Nat.mul_dvd_mul_iff_left two_pos).1 h2
    obtain ⟨i, hi⟩ := hdiv
    have htpow : t = (x₀ ^ m) ^ (2 ^ b * i) := by
      rw [← hk₁, hi, ← pow_mul]
      congr 1
      ring
    have hfus : ∀ g : G, g⁻¹ * x₀ ^ m * g ∉ Y := by
      intro g hg
      have hyM := hYM hg
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1
        (mem_powers_iff_mem_zpowers.2 ((hmemY _ hyM).1 hg))
      rw [← pow_mul] at hj
      have hyo : (g⁻¹ * x₀ ^ m * g) ^ (2 ^ (b + 1)) = 1 := by
        rw [inv_mul_mul_pow', ← hxo, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
      have hmj : m ∣ j := by
        have h1 : w ^ (2 * j * 2 ^ (b + 1)) = 1 := by
          rw [pow_mul, hj, hπpow, hπ1, hyo]
          exact one_mem L
        have h2 := orderOf_dvd_of_pow_eq_one h1
        rw [hw2, mul_comm (2 * j)] at h2
        exact (Nat.coprime_two_right.2 hm).dvd_of_dvd_mul_left
          ((Nat.mul_dvd_mul_iff_left (by positivity)).1 h2)
      apply hnot g
      have he : g⁻¹ * t * g = (g⁻¹ * x₀ ^ m * g) ^ (2 ^ b * i) := by
        rw [inv_mul_mul_pow', ← htpow]
      rw [he, ← hπ1 _ (pow_mem hyM _), ← hπpow _ hyM, ← hj, ← pow_mul]
      obtain ⟨j', rfl⟩ := hmj
      rw [← orderOf_dvd_iff_pow_eq_one, hw2]
      exact ⟨j' * i, by ring⟩
    exact F4Pilot.exists_normal_index_two_of_not_fused_of_relIndex_eq_two hYidx hodd hxM hxY hxo
      hmin hfus
  ·
    set Y := L ⊔ zpowers x₀
    have hYM : Y ≤ M := sup_le hLM (zpowers_le.2 hx₀)
    have htY : t ∉ Y := by
      intro htY
      obtain ⟨k, hk⟩ := hpowK t htM (hLK htY)
      rw [hwdef, hπpow, eq_comm, hπeq] at hk
      have hk' : x₀ ^ k ∈ L ⊔ zpowers t := by
        have h := mul_mem (mem_sup_right (mem_zpowers t) : t ∈ L ⊔ zpowers t)
          (mem_sup_left (inv_mem hk) : ((x₀ ^ k)⁻¹ * t)⁻¹ ∈ L ⊔ zpowers t)
        rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h
      rcases F4Pilot.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ht (hlift k hk') with h | h
      · rw [h, inv_one, one_mul] at hk
        exact htL hk
      · exact htx (h ▸ pow_mem (mem_zpowers x₀) k)
    have hYt : Y ⊔ zpowers t = M := le_antisymm (sup_le hYM (zpowers_le.2 htM)) hgen
    refine CFSG.SeitzReduction.exists_normal_index_two_of_not_fused ht
      (F4Pilot.mem_normalizer_of_le_centralizer_singleton (hYM.trans hM)) htY (by rwa [hYt])
      fun g hg => htY ?_
    have h := mul_mem (mem_sup_left (hA g (hYM hg)) : t * (g⁻¹ * t * g) ∈ Y) (inv_mem hg)
    rwa [mul_inv_cancel_right] at h

end Transfer

theorem exists_conj_eq_mul_of_forall_inner_of_odd_relIndex {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG : 2 < Nat.card G) {L M₀ : Subgroup G} {t : G} (ht : orderOf t = 2)
    (hLM : L ≤ M₀) (htM : t ∈ M₀) (hM : M₀ ≤ centralizer ({t} : Set G))
    (hodd : ¬ 2 ∣ M₀.relIndex (centralizer ({t} : Set G)))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L)
    (hinner : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ∈ L ⊔ zpowers t)
    {x₀ : G} (hx₀ : x₀ ∈ M₀) (hgen : M₀ ≤ L ⊔ zpowers x₀ ⊔ zpowers t)
    (hlift : ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have hLt : L ≤ centralizer ({t} : Set G) := hLM.trans hM
  have hA : ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → t * (g⁻¹ * t * g) ∈ L :=
    fun _ hg => F4Pilot.mul_conj_mem_of_forall_inner ht hLt hnot hinner hg
  by_cases h2 : 2 ∣ (centralizer ({t} : Set G)).index
  · exact F4Pilot.exists_conj_eq_mul_of_two_dvd_index ht hLt hA h2
  · have h2' : ¬ 2 ∣ M₀.index := by
      rw [← relIndex_mul_index hM]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
      · exact hodd h
      · exact h2 h
    exact absurd (exists_normal_index_two_of_forall_inner_of_odd_of_le ht hLM htM hM
        (hM.trans hCN) hnot (fun g hg => hA g (hM hg)) hx₀ hgen hlift h2')
      (CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG)

section Complement

variable {A B : Type*} [Group A] [Finite A] [Group B]

theorem exists_conj_complement_of_isPGroup {I : Subgroup A} [I.Normal] (Θ : A →* B)
    (hIΘ : I ≤ Θ.ker) (hodd : ∀ a ∈ Θ.ker, ∃ m : ℕ, Odd m ∧ a ^ m ∈ I)
    {φ : A} (hgen : ∀ a : A, ∃ κ ∈ Θ.ker, ∃ k : ℕ, a = κ * φ ^ k)
    (hφ : ∀ n : ℕ, Θ (φ ^ n) = 1 → φ ^ n = 1)
    {T : Subgroup A} (hT : IsPGroup 2 T) :
    ∃ φ' : A, (∀ y ∈ zpowers φ', y ∈ I → y = 1) ∧
      ∀ a ∈ T, ∃ c ∈ I, ∃ y ∈ zpowers φ', a = c * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' I with hπdef
  have hπ1 : ∀ a : A, π a = 1 ↔ a ∈ I := fun a => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨c, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos φ).ne'
  set φ₂ := φ ^ m with hφ₂def
  have hpowI : ∀ n : ℕ, φ ^ n ∈ I → φ ^ n = 1 := fun n hn => hφ n (hIΘ hn)
  set R : Subgroup (A ⧸ I) := zpowers (π φ₂) with hRdef
  have hRp : IsPGroup 2 R := by
    refine IsPGroup.of_card (n := c) ?_
    rw [Nat.card_zpowers]
    have h1 : orderOf φ₂ = 2 ^ c := by
      rw [hφ₂def, orderOf_pow_of_dvd hm.pos.ne' (hcm ▸ dvd_mul_left m _), hcm,
        Nat.mul_div_cancel _ hm.pos]
    have h2 : orderOf (π φ₂) = orderOf φ₂ := orderOf_eq_orderOf_iff.2 fun n => by
      rw [← map_pow, hπ1, hφ₂def, ← pow_mul]
      exact ⟨hpowI _, fun h => h ▸ I.one_mem⟩
    rw [h2, h1]
  obtain ⟨P₀, hRP₀⟩ := hRp.exists_le_sylow
  have hP₀R : (P₀ : Subgroup (A ⧸ I)) ≤ R := by
    intro x hx
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I x
    obtain ⟨κ, hκ, k, rfl⟩ := hgen α
    obtain ⟨e, he⟩ := P₀.isPGroup' ⟨_, hx⟩
    have he' : π (κ * φ ^ k) ^ 2 ^ e = 1 := congrArg Subtype.val he
    have h2 : (κ * φ ^ k) ^ 2 ^ e ∈ I := (hπ1 _).1 (by rw [map_pow]; exact he')
    have h3 : Θ (φ ^ (k * 2 ^ e)) = 1 := by
      have h := hIΘ h2
      rw [MonoidHom.mem_ker, map_pow, map_mul, MonoidHom.mem_ker.1 hκ, one_mul, ← map_pow,
        ← pow_mul] at h
      exact h
    have h5 : m ∣ k := by
      have h4 := orderOf_dvd_of_pow_eq_one (hφ _ h3)
      rw [hcm] at h4
      exact (Nat.Coprime.pow_right e (Nat.coprime_two_right.2 hm)).dvd_of_dvd_mul_right
        ((dvd_mul_left m _).trans h4)
    obtain ⟨k', rfl⟩ := h5
    have hφ₂P : π φ₂ ∈ (P₀ : Subgroup (A ⧸ I)) := hRP₀ (mem_zpowers _)
    have hsplit : π (κ * φ ^ (m * k')) = π κ * π φ₂ ^ k' := by
      rw [map_mul, hφ₂def, ← map_pow, ← pow_mul]
    have hκP : π κ ∈ (P₀ : Subgroup (A ⧸ I)) := by
      have h := mul_mem hx (inv_mem (pow_mem hφ₂P k'))
      rwa [hsplit, mul_inv_cancel_right] at h
    obtain ⟨m', hm', hκm'⟩ := hodd κ hκ
    obtain ⟨e', he''⟩ := P₀.isPGroup' ⟨_, hκP⟩
    have h6 : π κ ^ m' = 1 := by rw [← map_pow]; exact (hπ1 _).2 hκm'
    have h7 : π κ ^ 2 ^ e' = 1 := congrArg Subtype.val he''
    have h8 : π κ = 1 := by
      have hd : orderOf (π κ) ∣ Nat.gcd (2 ^ e') m' :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h7) (orderOf_dvd_of_pow_eq_one h6)
      rw [(Nat.Coprime.pow_left e' (Nat.coprime_two_left.2 hm')).gcd_eq_one,
        Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hd
    show π (κ * φ ^ (m * k')) ∈ R
    rw [hsplit, h8, one_mul]
    exact pow_mem (mem_zpowers _) k'
  obtain ⟨P₁, hTP₁⟩ := (hT.map π).exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (A ⧸ I) P₀ P₁
  obtain ⟨ψ, rfl⟩ := QuotientGroup.mk'_surjective I q
  refine ⟨ψ * φ₂ * ψ⁻¹, ?_, fun a ha => ?_⟩
  · rintro y ⟨z, rfl⟩ hy
    have hconj : (ψ * φ₂ * ψ⁻¹) ^ z = ψ * φ₂ ^ z * ψ⁻¹ := conj_zpow
    have hy' : ψ * φ₂ ^ z * ψ⁻¹ ∈ I := by
      have h : (ψ * φ₂ * ψ⁻¹) ^ z ∈ I := hy
      rwa [hconj] at h
    have hz : φ₂ ^ z ∈ I := by
      have h := (inferInstance : I.Normal).conj_mem _ hy' ψ⁻¹
      rwa [inv_inv, show ψ⁻¹ * (ψ * φ₂ ^ z * ψ⁻¹) * ψ = φ₂ ^ z by group] at h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2
      (show φ₂ ^ z ∈ zpowers φ from zpow_mem (pow_mem (mem_zpowers φ) m) z))
    have h1 : φ₂ ^ z = 1 := by rw [← hn] at hz ⊢; exact hpowI n hz
    show (ψ * φ₂ * ψ⁻¹) ^ z = 1
    rw [hconj, h1, mul_one, mul_inv_cancel]
  · have h1 : π a ∈ (P₁ : Subgroup (A ⧸ I)) := hTP₁ ⟨a, ha, rfl⟩
    rw [← hq, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨x, hx, hxa⟩ := h1
    obtain ⟨z, rfl⟩ := mem_zpowers_iff.1 (hP₀R hx)
    have hconj : (ψ * φ₂ * ψ⁻¹) ^ z = ψ * φ₂ ^ z * ψ⁻¹ := conj_zpow
    have hπy : π ((ψ * φ₂ * ψ⁻¹) ^ z) = π a := by
      rw [← hxa, hconj, map_mul, map_mul, map_inv, map_zpow, MulAut.smul_def, MulAut.conj_apply]
    refine ⟨a * ((ψ * φ₂ * ψ⁻¹) ^ z)⁻¹, (hπ1 _).1 ?_, (ψ * φ₂ * ψ⁻¹) ^ z,
      zpow_mem (mem_zpowers _) z, by rw [inv_mul_cancel_right]⟩
    rw [map_mul, map_inv, hπy, mul_inv_cancel]

end Complement

theorem exists_odd_relIndex_gen_of_mulAut {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {t : G} (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hLt : L ≤ centralizer ({t} : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcompl : ∀ T : Subgroup (MulAut L), IsPGroup 2 T → ∃ φ : MulAut L,
      (∀ y ∈ zpowers φ, y ∈ (MulAut.conj : L →* MulAut L).range → y = 1) ∧
      ∀ a ∈ T, ∃ c : L, ∃ y ∈ zpowers φ, a = MulAut.conj c * y) :
    ∃ M₀ : Subgroup G, L ≤ M₀ ∧ t ∈ M₀ ∧ M₀ ≤ centralizer ({t} : Set G) ∧
      ¬ 2 ∣ M₀.relIndex (centralizer ({t} : Set G)) ∧
      ∃ x₀ ∈ M₀, M₀ ≤ L ⊔ zpowers x₀ ⊔ zpowers t ∧
        ∀ n : ℕ, x₀ ^ n ∈ L ⊔ zpowers t → x₀ ^ n ∈ zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := inferInstance
  set M := centralizer ({t} : Set G) with hMdef
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  set I : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range with hIdef
  have hInorm : I.Normal := ⟨fun a ha ψ => by
    obtain ⟨c, rfl⟩ := ha
    refine ⟨ψ c, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]⟩
  set β : M →* MulAut L := L.normalizerMonoidHom.comp (inclusion hCN) with hβdef
  have hβ : ∀ (y : M) (a : L), ((β y a : L) : G) = y * a * (y : G)⁻¹ := fun y a =>
    normalizerMonoidHom_apply_apply_coe L _ a
  have hβL : ∀ c : L, β (inclusion hLt c) = MulAut.conj c := fun c => by
    ext a
    rw [hβ, MulAut.conj_apply]
    rfl
  have hβker : ∀ y : M, β y = 1 → (y : G) ∈ centralizer (L : Set G) := fun y hy => by
    rw [mem_centralizer_iff]
    intro a ha
    have h := hβ y ⟨a, ha⟩
    rw [hy, MulAut.one_apply] at h
    calc a * y = y * a * (y : G)⁻¹ * y := by rw [← h]
      _ = y * a := by group
  have hβt : β ⟨t, htM⟩ = 1 := by
    ext a
    rw [hβ, MulAut.one_apply]
    have h := mem_centralizer_singleton_iff.1 (hLt a.2)
    change t * a * t⁻¹ = a
    rw [← h, mul_inv_cancel_right]
  obtain ⟨P⟩ : Nonempty (Sylow 2 β.range) := inferInstance
  obtain ⟨φ, hφI, hTφ⟩ := hcompl ((P : Subgroup β.range).map β.range.subtype)
    (P.isPGroup'.map _)
  set B : Subgroup (MulAut L) := I ⊔ zpowers φ with hBdef
  have hmemB : ∀ x : MulAut L, x ∈ B ↔ ∃ c : L, ∃ y ∈ zpowers φ, x = MulAut.conj c * y := by
    intro x
    rw [← SetLike.mem_coe, hBdef, normal_mul, Set.mem_mul]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, y, hy, rfl⟩
      exact ⟨c, y, hy, rfl⟩
    · rintro ⟨c, y, hy, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, y, hy, rfl⟩
  set M₀ : Subgroup G := (B.comap β).map M.subtype with hM₀def
  have hmemM₀ : ∀ g (hg : g ∈ M), g ∈ M₀ ↔ β ⟨g, hg⟩ ∈ B := fun g hg =>
    (mem_map_iff_mem M.subtype_injective (x := ⟨g, hg⟩)).trans mem_comap
  have hM₀M : M₀ ≤ M := map_subtype_le _
  have hLM₀ : L ≤ M₀ := fun l hl => (hmemM₀ l (hLt hl)).2 (by
    rw [show (⟨l, hLt hl⟩ : M) = inclusion hLt ⟨l, hl⟩ from rfl, hβL]
    exact mem_sup_left ⟨⟨l, hl⟩, rfl⟩)
  have htM₀ : t ∈ M₀ := (hmemM₀ t htM).2 (by rw [hβt]; exact one_mem B)
  have hidx : ¬ 2 ∣ M₀.relIndex M := by
    have h1 : M₀.relIndex M = (B.comap β).index := by
      rw [relIndex, hM₀def, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
    have h2 : (B.comap β).index = (B.subgroupOf β.range).index := by
      rw [index_comap]
      rfl
    have hPB : (P : Subgroup β.range) ≤ B.subgroupOf β.range := by
      intro a ha
      rw [mem_subgroupOf, hmemB]
      exact hTφ a ⟨a, ha, rfl⟩
    rw [h1, h2]
    intro hdvd
    exact P.not_dvd_index (hdvd.trans (index_dvd_of_le hPB))
  set Φ := zpowers φ ⊓ β.range
  have : IsCyclic Φ := isCyclic_of_le inf_le_left
  obtain ⟨ψ₀, hψ₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Φ).1 inferInstance
  have hψ₀Φ : ψ₀ ∈ Φ := hψ₀ ▸ mem_zpowers ψ₀
  obtain ⟨x₀, hx₀⟩ := MonoidHom.mem_range.1 hψ₀Φ.2
  have hx₀M₀ : (x₀ : G) ∈ M₀ := (hmemM₀ x₀ x₀.2).2 (by
    rw [show (⟨(x₀ : G), x₀.2⟩ : M) = x₀ from rfl, hx₀]
    exact mem_sup_right hψ₀Φ.1)
  refine ⟨M₀, hLM₀, htM₀, hM₀M, hidx, x₀, hx₀M₀, fun g hg => ?_, fun n hn => ?_⟩
  ·
    have hgM := hM₀M hg
    obtain ⟨c, y, hy, hcy⟩ := (hmemB _).1 ((hmemM₀ g hgM).1 hg)
    have hyΦ : y ∈ Φ := ⟨hy, ⟨(inclusion hLt c)⁻¹ * ⟨g, hgM⟩, by
      rw [map_mul, map_inv, hβL, hcy, inv_mul_cancel_left]⟩⟩
    rw [← hψ₀] at hyΦ
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hyΦ
    set y' : M := (inclusion hLt c * x₀ ^ j)⁻¹ * ⟨g, hgM⟩ with hy'def
    have hy1 : β y' = 1 := by
      rw [hy'def, map_mul, map_inv, map_mul, map_zpow, hβL, hx₀, hj, ← hcy, inv_mul_cancel]
    have hyt : (y' : G) ∈ zpowers t := hKt ▸ ⟨hβker y' hy1, y'.2⟩
    have hg' : g = (c : G) * (x₀ : G) ^ j * y' := by
      rw [hy'def]
      simp only [coe_mul, coe_inv, coe_zpow, coe_inclusion]
      group
    rw [hg']
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left c.2))
      (mem_sup_left (mem_sup_right (zpow_mem (mem_zpowers _) j)))) (mem_sup_right hyt)
  ·
    set K₁ := (I.comap β).map M.subtype
    have hmemK₁ : ∀ y : M, (y : G) ∈ K₁ ↔ β y ∈ I :=
      fun y => (mem_map_iff_mem M.subtype_injective).trans mem_comap
    have hLK₁ : L ⊔ zpowers t ≤ K₁ :=
      sup_le (fun l hl => (hmemK₁ (inclusion hLt ⟨l, hl⟩)).2 ⟨⟨l, hl⟩, (hβL _).symm⟩)
        (zpowers_le.2 ((hmemK₁ ⟨t, htM⟩).2 ⟨1, by rw [hβt, map_one]⟩))
    have hx₀n : β (x₀ ^ n) ∈ I := (hmemK₁ (x₀ ^ n)).1 (by simpa using hLK₁ hn)
    have hβ1 : β (x₀ ^ n) = 1 := by
      have hmemφ : β (x₀ ^ n) ∈ zpowers φ := by
        rw [map_pow, hx₀]
        exact pow_mem hψ₀Φ.1 n
      exact hφI _ hmemφ hx₀n
    rw [← hKt]
    exact ⟨by simpa using hβker _ hβ1, by simpa using (x₀ ^ n).2⟩

end CFSG.SeitzReduction.TwistedE6Pilot
