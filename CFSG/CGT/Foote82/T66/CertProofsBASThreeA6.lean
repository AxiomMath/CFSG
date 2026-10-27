module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import CFSG.CGT.Foote82.T66.BASThreeA6Defs
import CFSG.CGT.Foote82.T66.CertProofsInvolAutA6
import CFSG.LocalAnalysis.ComponentClassification.AS81NXKernelCover
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix

public section

namespace CFSG.CGT.Foote82

open scoped commutatorElement

namespace BAS3A6

variable {G : Type*} [Group G]

theorem commutatorElement_inv_left {x y : G} (h : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h)
  calc ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
        rw [commutatorElement_def, commutatorElement_def]
        group
    _ = ⁅x, y⁆⁻¹ := by rw [mul_assoc, ← hc x, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_zpowers_of_zpow_mem {a b : G} (hob : orderOf b = 3) {n : ℤ}
    (hn : b ^ n ∈ Subgroup.zpowers a) (h3 : ¬ (3 : ℤ) ∣ n) : b ∈ Subgroup.zpowers a := by
  have h := Subgroup.zpow_mem _ hn n
  rw [← zpow_mul, ← zpow_mod_orderOf, hob] at h
  have hmod : n * n % ((3 : ℕ) : ℤ) = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    push_cast
    rcases this with h1 | h1
    · rw [Int.mul_emod, h1]; rfl
    · rw [Int.mul_emod, h1]; rfl
  rwa [hmod, zpow_one] at h

@[expose] def pairMap (a b : G) (p : Fin 3 × Fin 3) : G := a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)

theorem pairMap_mul {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a * b = b * a) (p q : Fin 3 × Fin 3) :
    pairMap a b p * pairMap a b q = pairMap a b (p + q) := by
  have hcomm : Commute a b := hab
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hpa : ∀ n : ℕ, a ^ (n % 3) = a ^ n := fun n => by rw [← hoa, pow_mod_orderOf]
  have hpb : ∀ n : ℕ, b ^ (n % 3) = b ^ n := fun n => by rw [← hob, pow_mod_orderOf]
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  show a ^ (i : ℕ) * b ^ (j : ℕ) * (a ^ (k : ℕ) * b ^ (l : ℕ)) =
    a ^ ((i + k : Fin 3) : ℕ) * b ^ ((j + l : Fin 3) : ℕ)
  rw [Fin.val_add, Fin.val_add, hpa, hpb, pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ (j : ℕ)),
    ← (hcomm.pow_pow (k : ℕ) (j : ℕ)).eq]
  group

theorem mem_closure_pair_iff {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a * b = b * a) (g : G) :
    g ∈ Subgroup.closure ({a, b} : Set G) ↔ ∃ p, pairMap a b p = g := by
  have hmulf := pairMap_mul ha3 hb3 ha1 hb1 hab
  have h3p : ∀ p : Fin 3 × Fin 3, p + (p + p) = 0 := by decide
  have hf0 : pairMap a b 0 = 1 := by simp [pairMap]
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨(1, 0), by simp [pairMap]⟩
      · exact ⟨(0, 1), by simp [pairMap]⟩
    | one => exact ⟨0, hf0⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, (hmulf p q).symm⟩
    | inv x _ hx =>
      obtain ⟨p, rfl⟩ := hx
      refine ⟨p + p, ?_⟩
      rw [← hmulf]
      refine (inv_eq_of_mul_eq_one_right ?_).symm
      rw [hmulf, hmulf, h3p, hf0]
  · rintro ⟨⟨i, j⟩, rfl⟩
    have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ ha _) (Subgroup.pow_mem _ hb _)

theorem card_closure_pair {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hb : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  have hcomm : Commute a b := hab
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hmem := mem_closure_pair_iff ha3 hb3 ha1 hb1 hab
  have hf : Function.Injective (pairMap a b) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) := h
    have hjl : j = l := by
      by_contra hne
      apply hb
      have hb' : b ^ ((j : ℕ) - (l : ℤ)) ∈ Subgroup.zpowers a := by
        have e : b ^ ((j : ℕ) - (l : ℤ)) = (a ^ (i : ℕ))⁻¹ * a ^ (k : ℕ) := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          calc b ^ (j : ℕ) * (b ^ (l : ℕ))⁻¹
              = (a ^ (i : ℕ))⁻¹ * (a ^ (i : ℕ) * b ^ (j : ℕ)) * (b ^ (l : ℕ))⁻¹ := by group
            _ = (a ^ (i : ℕ))⁻¹ * (a ^ (k : ℕ) * b ^ (l : ℕ)) * (b ^ (l : ℕ))⁻¹ := by rw [h']
            _ = (a ^ (i : ℕ))⁻¹ * a ^ (k : ℕ) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
          (Subgroup.npow_mem_zpowers _ _)
      refine mem_zpowers_of_zpow_mem hob hb' ?_
      intro h3
      apply hne
      apply Fin.ext
      have := j.2
      have := l.2
      omega
    subst hjl
    have hik : a ^ (i : ℕ) = a ^ (k : ℕ) := mul_right_cancel h'
    rw [pow_eq_pow_iff_modEq, hoa] at hik
    have := Nat.ModEq.eq_of_lt_of_lt hik i.2 k.2
    rw [Fin.ext this]
  have hbij : Function.Bijective fun p : Fin 3 × Fin 3 =>
      (⟨pairMap a b p, (hmem _).mpr ⟨p, rfl⟩⟩ : Subgroup.closure ({a, b} : Set G)) :=
    ⟨fun p q h => hf (congrArg Subtype.val h), fun x => by
      obtain ⟨p, hp⟩ := (hmem x).mp x.2
      exact ⟨p, Subtype.ext hp⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin]

theorem orderOf_eq_six {x : G} (h6 : x ^ 6 = 1) (h2 : x ^ 2 ≠ 1) (h3 : x ^ 3 ≠ 1) :
    orderOf x = 6 := by
  have hd : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hle : orderOf x ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr ⟨6, by norm_num, (isPeriodicPt_mul_iff_pow_eq_one x).mpr h6⟩
  interval_cases h : orderOf x
  · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_pow]) h2
  · exact absurd (by rw [← h]; exact pow_orderOf_eq_one x) h2
  · exact absurd (by rw [← h]; exact pow_orderOf_eq_one x) h3
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · rfl

end BAS3A6

open BAS3A6

theorem basThreeA6_of_cases (hA6 : InvolAutA6Cases) :
    BASThreeA6 := by
  intro Y _ _ α hα hperf hcen hodd hne δ hδ2 hδ1
  haveI : Group.IsPerfect Y := ⟨hperf⟩
  have hZ3 : Nat.card α.ker = 3 := by
    have h6 : Nat.card α.ker ∣ 6 :=
      CFSG.ComponentClassification.AS81.NXKernel.card_ker_dvd_six α hα hcen
    have hne1 : Nat.card α.ker ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
    have hle : Nat.card α.ker ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    obtain ⟨k, hk⟩ := hodd
    interval_cases h : Nat.card α.ker <;> omega
  have hcA6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hcZ : Subgroup.center Y ≤ α.ker := by
    intro y hy
    rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hcA6, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := hα g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hy g')]
  have hδZ : ∀ z ∈ α.ker, δ z ∈ α.ker := fun z hz => hcZ (by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := δ.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hcen hz) g')])
  have hmapZ : α.ker.map δ.toMonoidHom = α.ker := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hδZ z hz
    · intro z hz
      exact ⟨δ z, hδZ z hz, hδ2 z⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective α hα
  let δq : Y ⧸ α.ker ≃* Y ⧸ α.ker := QuotientGroup.congr α.ker α.ker δ hmapZ
  let θ : MulAut (alternatingGroup (Fin 6)) := e.symm.trans (δq.trans e)
  have hθ : ∀ y, θ (α y) = α (δ y) := by
    intro y
    have h1 : e.symm (α y) = (QuotientGroup.mk y : Y ⧸ α.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show e (δq (e.symm (α y))) = α (δ y)
    rw [h1]
    rfl
  have hθ2 : ∀ g, θ (θ g) = g := fun g => by
    obtain ⟨y, rfl⟩ := hα g
    rw [hθ, hθ, hδ2]
  have hθ1 : ∃ g, θ g ≠ g := by
    by_contra hall
    push_neg at hall
    have hZy : ∀ y : Y, y⁻¹ * δ y ∈ α.ker := fun y => by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hθ, hall, inv_mul_cancel]
    let f : Y →* ↥(Subgroup.center Y) :=
      { toFun := fun y => ⟨y⁻¹ * δ y, hcen (hZy y)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          have hc := Subgroup.mem_center_iff.mp (hcen (hZy x))
          show (x * y)⁻¹ * δ (x * y) = x⁻¹ * δ x * (y⁻¹ * δ y)
          rw [map_mul]
          calc (x * y)⁻¹ * (δ x * δ y) = y⁻¹ * (x⁻¹ * δ x) * δ y := by group
            _ = (x⁻¹ * δ x) * y⁻¹ * δ y := by rw [← hc y⁻¹]
            _ = x⁻¹ * δ x * (y⁻¹ * δ y) := by group) }
    have hker := Abelianization.commutator_subset_ker f
    rw [show commutator Y = ⊤ from hperf] at hker
    obtain ⟨y, hy⟩ := hδ1
    have h1 := hker (Subgroup.mem_top y)
    rw [MonoidHom.mem_ker] at h1
    have h2 : y⁻¹ * δ y = 1 := congrArg Subtype.val h1
    exact hy (by rw [← mul_left_cancel_iff (a := y⁻¹), h2, inv_mul_cancel])
  have hZpow : ∀ z ∈ α.ker, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := α.ker) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  have hlift : ∀ y : Y, α (δ y * y⁻¹) = θ (α y) * (α y)⁻¹ := fun y => by
    rw [map_mul, map_inv, hθ]
  rcases hA6 θ hθ2 hθ1 with ⟨g, hg4⟩ | ⟨a, b, g, ha3, hb3, ha1, hab, hb, hθab, hg2⟩
  ·
    obtain ⟨y, rfl⟩ := hα g
    refine ⟨y, ?_⟩
    have h4 : 4 ∣ orderOf (δ y * y⁻¹) := by
      rw [← hg4, ← hlift]
      exact orderOf_map_dvd α _
    have hpos := orderOf_pos (δ y * y⁻¹)
    obtain ⟨k, hk⟩ := h4
    exact ⟨by omega, ⟨2 * k, by omega⟩⟩
  ·
    obtain ⟨a', rfl⟩ := hα a
    obtain ⟨b', rfl⟩ := hα b
    have hzZ : ⁅a', b'⁆ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hab]
    have hzc : ⁅a', b'⁆ ∈ Subgroup.center Y := hcen hzZ
    have hb1 : α b' ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
    have hcentral : ∀ {n : Y}, n ∈ α.ker → ∀ x : Y, Commute n x := fun hn x =>
      (Subgroup.mem_center_iff.mp (hcen hn) x).symm
    have hz1 : ⁅a', b'⁆ ≠ 1 := by
      intro hz
      have hc' : Commute a' b' := commutatorElement_eq_one_iff_mul_comm.mp hz
      set S := Subgroup.closure ({α a', α b'} : Set (alternatingGroup (Fin 6))) with hS
      set P := S.comap α with hP
      have hrep : ∀ x ∈ P, ∃ (i j : ℕ) (n : Y), n ∈ α.ker ∧ x = a' ^ i * b' ^ j * n := by
        intro x hx
        obtain ⟨⟨i, j⟩, hij⟩ := (mem_closure_pair_iff ha3 hb3 ha1 hb1 hab (α x)).mp hx
        refine ⟨i, j, (a' ^ (i : ℕ) * b' ^ (j : ℕ))⁻¹ * x, ?_, by group⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_pow, map_pow, ← hij]
        simp [pairMap]
      have hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
        intro p hp q hq
        obtain ⟨i, j, n, hn, rfl⟩ := hrep p hp
        obtain ⟨k, l, m, hm, rfl⟩ := hrep q hq
        have hAB : Commute (a' ^ i * b' ^ j) (a' ^ k * b' ^ l) :=
          (((Commute.refl a').pow_pow i k).mul_right (hc'.pow_pow i l)).mul_left
            ((hc'.symm.pow_pow j k).mul_right ((Commute.refl b').pow_pow j l))
        exact ((hAB.mul_right (hcentral hm _).symm).mul_left
          ((hcentral hn _).mul_right (hcentral hn m))).eq
      letI : CommGroup ↥P :=
        { (inferInstance : Group ↥P) with mul_comm := fun p q => Subtype.ext (hPcomm p p.2 q q.2) }
      have hSc : Nat.card S = 9 := card_closure_pair ha3 hb3 ha1 hab hb
      have hA6c : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have hSi : S.index = 40 := by
        have := Subgroup.index_mul_card S
        rw [hSc, hA6c] at this
        omega
      have hPi : P.index = 40 := by rw [hP, Subgroup.index_comap_of_surjective S hα, hSi]
      obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
      have hT := MonoidHom.transfer_eq_pow (A := ↥P) (MonoidHom.id ↥P) z₀ (fun k g₀ _ => by
        rw [mul_assoc, ((hcentral hz₀ g₀).pow_left k).eq, ← mul_assoc, inv_mul_cancel, one_mul])
      have hT1 : MonoidHom.transfer (A := ↥P) (MonoidHom.id ↥P) z₀ = 1 := by
        have h := Abelianization.commutator_subset_ker
          (MonoidHom.transfer (A := ↥P) (MonoidHom.id ↥P))
        rw [show commutator Y = ⊤ from hperf] at h
        exact h (Subgroup.mem_top z₀)
      rw [hT1] at hT
      have h40 : z₀ ^ P.index = 1 := (congrArg Subtype.val hT).symm
      rw [hPi] at h40
      have h3 := hZpow z₀ hz₀
      apply hz₀1'
      calc z₀ = z₀ ^ (3 * 13 + 1) := by rw [pow_succ, pow_mul, h3, one_pow, one_mul]
        _ = 1 := h40
    have hδz : δ ⁅a', b'⁆ = ⁅a', b'⁆⁻¹ := by
      rw [map_commutatorElement]
      rcases hθab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hn₁ : a' * δ a' ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, ← hθ, h1, mul_inv_cancel]
        have hn₂ : b'⁻¹ * δ b' ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hθ, h2, inv_mul_cancel]
        rw [show δ a' = a'⁻¹ * (a' * δ a') by group, show δ b' = b' * (b'⁻¹ * δ b') by group,
          CFSG.HardMathSupport.Solomon.Coordinator.commutator_mul_central (hcen hn₁) (hcen hn₂),
          commutatorElement_inv_left hzc]
      · have hn₁ : b'⁻¹ * δ a' ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hθ, h1, inv_mul_cancel]
        have hn₂ : a'⁻¹ * δ b' ∈ α.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hθ, h2, inv_mul_cancel]
        rw [show δ a' = b' * (b'⁻¹ * δ a') by group, show δ b' = a' * (a'⁻¹ * δ b') by group,
          CFSG.HardMathSupport.Solomon.Coordinator.commutator_mul_central (hcen hn₁) (hcen hn₂),
          commutatorElement_inv]
    set z := ⁅a', b'⁆ with hzdef
    have hz3 : z ^ 3 = 1 := hZpow z hzZ
    have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have hZz : ∀ x ∈ α.ker, x = 1 ∨ x = z ∨ x = z ^ 2 := by
      intro x hx
      have hle : Subgroup.zpowers z ≤ α.ker := Subgroup.zpowers_le_of_mem hzZ
      have heq : Subgroup.zpowers z = α.ker := by
        apply Subgroup.eq_of_le_of_card_ge hle
        rw [hZ3, Nat.card_zpowers, hoz]
      rw [← heq] at hx
      obtain ⟨k, rfl⟩ := hx
      simp only
      rw [← zpow_mod_orderOf, hoz]
      have : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
      rcases this with h | h | h <;> rw [h]
      · left; exact zpow_zero z
      · right; left; exact zpow_one z
      · right; right; exact zpow_two z |>.trans (pow_two z).symm
    obtain ⟨y, rfl⟩ := hα g
    set w := δ y * y⁻¹ with hw
    have hαw : α w = θ (α y) * (α y)⁻¹ := hlift y
    have hαw1 : α w ≠ 1 := by
      intro h
      rw [h] at hαw
      rw [← hαw, orderOf_one] at hg2
      exact absurd hg2 (by norm_num)
    have hw1 : w ≠ 1 := fun h => hαw1 (by rw [h, map_one])
    have hw2 : w ^ 2 ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_pow, hαw, ← hg2, pow_orderOf_eq_one]
    have hzc' : ∀ x : Y, Commute z x := hcentral hzZ
    have hz2 : z ^ 2 ≠ 1 := by
      intro h
      apply hz1
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3, h, inv_one, one_mul]
    have hαz : ∀ k : ℕ, α (w * z ^ k) = α w := fun k => by
      rw [map_mul, map_pow, MonoidHom.mem_ker.mp hzZ, one_pow, mul_one]
    have hfin : ∀ x : Y, orderOf x = 6 → 2 < orderOf x ∧ Even (orderOf x) := fun x h =>
      ⟨by omega, ⟨3, by omega⟩⟩
    rcases hZz _ hw2 with h | h | h
    ·
      refine ⟨y * z, hfin _ ?_⟩
      have hyz : δ (y * z) * (y * z)⁻¹ = w * z := by
        rw [map_mul, hδz, mul_inv_rev]
        calc δ y * z⁻¹ * (z⁻¹ * y⁻¹) = δ y * (z⁻¹ * z⁻¹) * y⁻¹ := by group
          _ = δ y * z * y⁻¹ := by
              rw [show z⁻¹ * z⁻¹ = z by
                calc z⁻¹ * z⁻¹ = z⁻¹ * z⁻¹ * z ^ 3 := by rw [hz3, mul_one]
                  _ = z := by group]
          _ = δ y * y⁻¹ * z := by rw [mul_assoc, (hzc' y⁻¹).eq, ← mul_assoc]
      rw [hyz]
      refine orderOf_eq_six ?_ ?_ ?_
      · rw [(hzc' w).symm.mul_pow, show 6 = 2 * 3 from rfl, pow_mul, pow_mul, h, one_pow,
          ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hz3, one_pow, one_mul]
      · rw [(hzc' w).symm.mul_pow, h, one_mul]
        exact hz2
      · rw [(hzc' w).symm.mul_pow, hz3, mul_one, pow_succ, h, one_mul]
        exact hw1
    ·
      refine ⟨y, hfin _ ?_⟩
      refine orderOf_eq_six ?_ ?_ ?_
      · rw [show 6 = 2 * 3 from rfl, pow_mul, h, hz3]
      · rw [h]
        exact hz1
      · intro h3
        apply hαw1
        have : α (w ^ 3) = α w := by
          rw [pow_succ, map_mul, MonoidHom.mem_ker.mp hw2, one_mul]
        rw [← this, h3, map_one]
    ·
      refine ⟨y, hfin _ ?_⟩
      refine orderOf_eq_six ?_ ?_ ?_
      · rw [show 6 = 2 * 3 from rfl, pow_mul, h, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul,
          hz3, one_pow]
      · rw [h]
        exact hz2
      · intro h3
        apply hαw1
        have : α (w ^ 3) = α w := by
          rw [pow_succ, map_mul, MonoidHom.mem_ker.mp hw2, one_mul]
        rw [← this, h3, map_one]

theorem basThreeA6_holds :
    BASThreeA6 :=
  basThreeA6_of_cases involAutA6Cases_holds

end CFSG.CGT.Foote82
