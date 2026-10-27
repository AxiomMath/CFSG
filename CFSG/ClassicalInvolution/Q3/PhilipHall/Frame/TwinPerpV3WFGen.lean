module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFCore
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFF4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Gen

variable {Y : Type} [Group Y] [Finite Y]

theorem klein_comm {t s : Y} (hc : t * s = s * t) :
    ∀ g h : Y, (g = 1 ∨ g = t ∨ g = s ∨ g = t * s) → (h = 1 ∨ h = t ∨ h = s ∨ h = t * s) →
      g * h = h * g := by
  have ct : Commute t t := Commute.refl t
  have cs : Commute s s := Commute.refl s
  have cts : Commute t s := hc
  have cst : Commute s t := hc.symm
  have c3 : Commute t (t * s) := ct.mul_right cts
  have c4 : Commute s (t * s) := cst.mul_right cs
  have c5 : Commute (t * s) t := c3.symm
  have c6 : Commute (t * s) s := c4.symm
  have c7 : Commute (t * s) (t * s) := Commute.refl _
  rintro g h (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
    first | rfl | simp | exact cts.eq | exact cst.eq | exact c3.eq | exact c4.eq | exact c5.eq |
      exact c6.eq


theorem c7_core {s t b₁ b₂ : Y} {J : Fin 4 → Subgroup Y} {N : Subgroup Y}
    (hq : ∀ i, Q8Facts (J i) s) (hcom : ∀ i j, i ≠ j → Commutes (J i) (J j))
    (hJinj : Function.Injective J) (hNC : N ≤ Subgroup.centralizer ({s} : Set Y))
    (hNn : (N.subgroupOf (Subgroup.centralizer ({s} : Set Y))).Normal)
    (hPN : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ N)
    (hPC : ∀ c ∈ Subgroup.centralizer ({s} : Set Y), ∀ p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3,
      c * p * c⁻¹ ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
    (hodd : ∀ g ∈ N, ∃ m : ℕ, Odd m ∧ g ^ m ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3)
    (hb₁ : b₁ ∈ Subgroup.centralizer ({s} : Set Y)) (hb₂ : b₂ ∈ Subgroup.centralizer ({s} : Set Y))
    (hb11 : b₁ * b₁ = 1) (hb22 : b₂ * b₂ = 1) (hb12 : b₁ * b₂ = b₂ * b₁)
    (hperm : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), ∀ i, ∃ j, conjSub b (J i) = J j)
    (hmove : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), ∀ i, conjSub b (J i) ≠ J i)
    (hG : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), ∀ c ∈ Subgroup.centralizer ({s} : Set Y),
      c * b = b * c → c * t = t * c) :
    ∀ ℓ ∈ N, ∃ r ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3, ∃ c ∈ N, c * t = t * c ∧ ℓ = r * c := by
  classical
  set C := Subgroup.centralizer ({s} : Set Y) with hC
  set P := J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 with hP
  have hPle : P ≤ C := P_le_centralizer hq
  let Q : Subgroup Y :=
    { carrier := {ℓ | ∃ r ∈ P, ∃ c ∈ N, c * t = t * c ∧ ℓ = r * c}
      mul_mem' := by
        rintro _ _ ⟨r₁, hr₁, c₁, hc₁, hc₁t, rfl⟩ ⟨r₂, hr₂, c₂, hc₂, hc₂t, rfl⟩
        refine ⟨r₁ * (c₁ * r₂ * c₁⁻¹), P.mul_mem hr₁ (hPC c₁ (hNC hc₁) r₂ hr₂), c₁ * c₂,
          N.mul_mem hc₁ hc₂, ?_, by group⟩
        calc c₁ * c₂ * t = c₁ * (c₂ * t) := mul_assoc _ _ _
          _ = c₁ * (t * c₂) := by rw [hc₂t]
          _ = (c₁ * t) * c₂ := (mul_assoc _ _ _).symm
          _ = (t * c₁) * c₂ := by rw [hc₁t]
          _ = t * (c₁ * c₂) := mul_assoc _ _ _
      one_mem' := ⟨1, P.one_mem, 1, N.one_mem, by simp, by simp⟩
      inv_mem' := by
        rintro _ ⟨r, hr, c, hc, hct, rfl⟩
        refine ⟨c⁻¹ * r⁻¹ * c⁻¹⁻¹, hPC c⁻¹ (hNC (N.inv_mem hc)) r⁻¹ (P.inv_mem hr), c⁻¹,
          N.inv_mem hc, ?_, by group⟩
        have := congrArg (fun g => c⁻¹ * g * c⁻¹) hct
        simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] at this
        calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
          _ = t * c⁻¹ := by group }
  have hPQ : P ≤ Q := fun r hr => ⟨r, hr, 1, N.one_mem, by simp, by simp⟩
  have hQN : Q ≤ N := by
    rintro _ ⟨r, hr, c, hc, -, rfl⟩
    exact N.mul_mem (hPN hr) hc
  have hs2 : s * s = 1 := (hq 0).z_sq
  have hb12sq : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
      _ = b₁ * (b₁ * b₂) * b₂ := by rw [← hb12]
      _ = (b₁ * b₁) * (b₂ * b₂) := by group
      _ = 1 := by rw [hb11, hb22, one_mul]
  have hb12C : b₁ * b₂ ∈ C := C.mul_mem hb₁ hb₂
  have hclass : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), ∀ ℓ ∈ N, b * ℓ * b⁻¹ * ℓ⁻¹ ∈ P → ℓ ∈ Q := by
    intro b hb ℓ hℓ hcomm
    have hbC : b ∈ C := by
      rcases hb with rfl | rfl | rfl
      · exact hb₁
      · exact hb₂
      · exact hb12C
    have hb2 : b * b = 1 := by
      rcases hb with rfl | rfl | rfl
      · exact hb11
      · exact hb22
      · exact hb12sq
    exact c7_class hq hcom hJinj hb2 (Subgroup.mem_centralizer_singleton_iff.mp hbC) (hperm b hb)
      (hmove b hb) hNC hPN hodd (hG b hb) hℓ hcomm
  haveI hPnorm : (P.subgroupOf C).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hPC g g.2 a ha⟩
  let mk : ↥C →* (↥C ⧸ P.subgroupOf C) := QuotientGroup.mk' (P.subgroupOf C)
  have hmk : ∀ x y : ↥C, mk x = mk y ↔ (x⁻¹ * y : ↥C) ∈ P.subgroupOf C := fun x y => QuotientGroup.eq
  let ub₁ : ↥C := ⟨b₁, hb₁⟩
  let ub₂ : ↥C := ⟨b₂, hb₂⟩
  have hmk1 : ∀ x : ↥C, mk x = 1 ↔ (x : Y) ∈ P := fun x => by
    show (QuotientGroup.mk x : ↥C ⧸ P.subgroupOf C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hnotP : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), b ∉ P := fun b hb hbP =>
    hmove b hb 0 (P_normalizes hcom 0 hbP)
  have h1ne : mk ub₁ ≠ 1 := fun h => hnotP b₁ (by simp) ((hmk1 ub₁).mp h)
  have h2ne : mk ub₂ ≠ 1 := fun h => hnotP b₂ (by simp) ((hmk1 ub₂).mp h)
  have hq1 : mk ub₁ * mk ub₁ = 1 := by
    rw [← map_mul]
    have : ub₁ * ub₁ = 1 := Subtype.ext hb11
    rw [this, map_one]
  have hq2 : mk ub₂ * mk ub₂ = 1 := by
    rw [← map_mul]
    have : ub₂ * ub₂ = 1 := Subtype.ext hb22
    rw [this, map_one]
  have hc12 : mk ub₁ * mk ub₂ = mk ub₂ * mk ub₁ := by
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext hb12)
  have h12ne : mk ub₁ * mk ub₂ ≠ 1 := fun h => hnotP (b₁ * b₂) (by simp) ((hmk1 (ub₁ * ub₂)).mp (by
    rw [map_mul]; exact h))
  let A : Subgroup (↥C ⧸ P.subgroupOf C) := Subgroup.closure {mk ub₁, mk ub₂}
  have hAel : ∀ a ∈ A, a = 1 ∨ a = mk ub₁ ∨ a = mk ub₂ ∨ a = mk ub₁ * mk ub₂ :=
    klein_closure hq1 hq2 hc12
  have hAab : CFSG.Open.IsElemAbelian 2 A := by
    refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      klein_comm hc12 a b (hAel a ha) (hAel b hb), fun x hx => ?_⟩
    rcases hAel x hx with rfl | rfl | rfl | rfl
    · simp
    · rw [sq]; exact hq1
    · rw [sq]; exact hq2
    · rw [sq]
      calc mk ub₁ * mk ub₂ * (mk ub₁ * mk ub₂) = mk ub₁ * (mk ub₂ * mk ub₁) * mk ub₂ := by group
        _ = mk ub₁ * (mk ub₁ * mk ub₂) * mk ub₂ := by rw [← hc12]
        _ = (mk ub₁ * mk ub₁) * (mk ub₂ * mk ub₂) := by group
        _ = 1 := by rw [hq1, hq2, one_mul]
  have hmemA₁ : mk ub₁ ∈ A := Subgroup.subset_closure (by simp)
  have hmemA₂ : mk ub₂ ∈ A := Subgroup.subset_closure (by simp)
  have h4 : 2 ^ 2 ≤ Nat.card A := by
    have hsub : ({1, mk ub₁, mk ub₂, mk ub₁ * mk ub₂} : Set (↥C ⧸ P.subgroupOf C)) ⊆ A := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact A.one_mem
      · exact hmemA₁
      · exact hmemA₂
      · exact A.mul_mem hmemA₁ hmemA₂
    have h12 : mk ub₁ ≠ mk ub₂ := fun h => by
      apply h12ne
      calc mk ub₁ * mk ub₂ = mk ub₂ * mk ub₂ := by rw [h]
        _ = 1 := hq2
    have n1 : (1 : ↥C ⧸ P.subgroupOf C) ∉ ({mk ub₁, mk ub₂, mk ub₁ * mk ub₂} : Set _) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm h1ne, Ne.symm h2ne, Ne.symm h12ne⟩
    have n2 : mk ub₁ ∉ ({mk ub₂, mk ub₁ * mk ub₂} : Set (↥C ⧸ P.subgroupOf C)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨h12, fun h => h2ne ?_⟩
      calc mk ub₂ = (mk ub₁)⁻¹ * (mk ub₁ * mk ub₂) := by group
        _ = (mk ub₁)⁻¹ * mk ub₁ := by rw [← h]
        _ = 1 := by group
    have n3 : mk ub₂ ∉ ({mk ub₁ * mk ub₂} : Set (↥C ⧸ P.subgroupOf C)) := by
      simp only [Set.mem_singleton_iff]
      intro h
      apply h1ne
      calc mk ub₁ = (mk ub₁ * mk ub₂) * (mk ub₂)⁻¹ := by group
        _ = mk ub₂ * (mk ub₂)⁻¹ := by rw [← h]
        _ = 1 := by group
    have hca : ({1, mk ub₁, mk ub₂, mk ub₁ * mk ub₂} : Set (↥C ⧸ P.subgroupOf C)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
        Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
    calc 2 ^ 2 = ({1, mk ub₁, mk ub₂, mk ub₁ * mk ub₂} : Set (↥C ⧸ P.subgroupOf C)).ncard := by
          rw [hca]; norm_num
      _ ≤ (A : Set (↥C ⧸ P.subgroupOf C)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card A := (Nat.card_coe_set_eq (A : Set (↥C ⧸ P.subgroupOf C))).symm
  let N' : Subgroup ↥C := N.subgroupOf C
  let X : Subgroup (↥C ⧸ P.subgroupOf C) := N'.map mk
  have hXn : X.Normal := Subgroup.Normal.map hNn mk (QuotientGroup.mk'_surjective _)
  have hAX : A ≤ Subgroup.normalizer (X : Set (↥C ⧸ P.subgroupOf C)) := by
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hXn.conj_mem h hh a
    · intro hh
      have := hXn.conj_mem _ hh a⁻¹
      simpa [mul_assoc] using this
  have hcop : Nat.Coprime 2 (Nat.card X) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 hdvd
    obtain ⟨n', hn'N', hn'⟩ := x.2
    obtain ⟨m, hm, hmP⟩ := hodd n'.1 (Subgroup.mem_subgroupOf.mp hn'N')
    have hxm : (x : ↥C ⧸ P.subgroupOf C) ^ m = 1 := by
      rw [← hn', ← map_pow, hmk1]
      simpa using hmP
    have hord : orderOf x ∣ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply Subtype.ext
      simpa using hxm
    rw [hx] at hord
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hord)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity (p := 2)
    Nat.prime_two hAab h4 hAX hcop
  let Qbar : Subgroup (↥C ⧸ P.subgroupOf C) := (Q.subgroupOf C).map mk
  have hkey : ∀ b ∈ ({b₁, b₂, b₁ * b₂} : Set Y), ∀ hbC : b ∈ C, ∀ n' : ↥C, n' ∈ N' →
      mk n' * mk ⟨b, hbC⟩ = mk ⟨b, hbC⟩ * mk n' → mk n' ∈ Qbar := by
    intro b hb hbC n' hn' hc
    rw [← map_mul, ← map_mul, hmk] at hc
    have hℓ : n'.1 ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hu : (b⁻¹ * n'.1⁻¹ * b * n'.1) ∈ P := by
      have := Subgroup.mem_subgroupOf.mp hc
      simpa [mul_assoc] using this
    have hcomm : b * n'.1 * b⁻¹ * n'.1⁻¹ ∈ P := by
      have := hPC (n'.1 * b) (C.mul_mem (hNC hℓ) hbC) _ hu
      have e : n'.1 * b * (b⁻¹ * n'.1⁻¹ * b * n'.1) * (n'.1 * b)⁻¹ = b * n'.1 * b⁻¹ * n'.1⁻¹ := by
        group
      rwa [e] at this
    have hQ := hclass b hb n'.1 hℓ hcomm
    exact ⟨n', Subgroup.mem_subgroupOf.mpr hQ, rfl⟩
  have hXQ : X ≤ Qbar := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun haA => iSup_le fun ha1 => ?_
    rintro x ⟨hxX, hxc⟩
    have hxc' : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    obtain ⟨n', hn', rfl⟩ := hxX
    rcases hAel a haA with h | h | h | h
    · exact absurd h ha1
    · subst h
      exact hkey b₁ (by simp) hb₁ n' hn' hxc'
    · subst h
      exact hkey b₂ (by simp) hb₂ n' hn' hxc'
    · subst h
      have : mk ub₁ * mk ub₂ = mk ⟨b₁ * b₂, hb12C⟩ := by
        rw [← map_mul]; rfl
      rw [this] at hxc'
      exact hkey (b₁ * b₂) (by simp) hb12C n' hn' hxc'
  intro ℓ hℓ
  have hℓC : ℓ ∈ C := hNC hℓ
  have hx : mk ⟨ℓ, hℓC⟩ ∈ X := ⟨⟨ℓ, hℓC⟩, Subgroup.mem_subgroupOf.mpr hℓ, rfl⟩
  obtain ⟨q', hq'Q, hq'⟩ := hXQ hx
  have h := (hmk _ _).mp hq'
  have hpP : (q'.1)⁻¹ * ℓ ∈ P := Subgroup.mem_subgroupOf.mp h
  have hq'Q' : q'.1 ∈ Q := Subgroup.mem_subgroupOf.mp hq'Q
  have e : ℓ = q'.1 * ((q'.1)⁻¹ * ℓ) := by group
  have hℓQ : ℓ ∈ Q := by rw [e]; exact Q.mul_mem hq'Q' (hPQ hpP)
  exact hℓQ

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
