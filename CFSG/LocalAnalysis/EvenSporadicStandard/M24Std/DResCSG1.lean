module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHSext3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHLevelCA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Sign
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSK

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

section Abstract

theorem alt6_commutator_sub :
    ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ = alternatingGroup (Fin 6) := by
  have h : ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))), ⊤⁆ = ⊤ := alt6_commutator
  have h2 := congrArg (Subgroup.map (alternatingGroup (Fin 6)).subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

theorem perfect_comap_alt6 {K : Type} [Group K] (φ : K →* Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3) {a b : K}
    (ha : φ a ∈ alternatingGroup (Fin 6)) (hb : φ b ∈ alternatingGroup (Fin 6))
    (hab : ⁅a, b⁆ ∈ φ.ker) (hab1 : ⁅a, b⁆ ≠ 1) :
    ⁅(alternatingGroup (Fin 6)).comap φ, (alternatingGroup (Fin 6)).comap φ⁆ =
      (alternatingGroup (Fin 6)).comap φ := by
  set Q := (alternatingGroup (Fin 6)).comap φ with hQ
  refine le_antisymm (commutator_le_self Q) ?_
  have hmapP : (⁅Q, Q⁆).map φ = alternatingGroup (Fin 6) := by
    rw [Subgroup.map_commutator, hQ, Subgroup.map_comap_eq_self_of_surjective hφ,
      alt6_commutator_sub]
  have hZ : φ.ker ≤ ⁅Q, Q⁆ := by
    have hmem : ⁅a, b⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator ha hb
    have := DResH.LevelC.zpowers_eq_of_card_three hk hab hab1
    rw [← this]
    exact (zpowers_le).2 hmem
  intro q hq
  have : φ q ∈ (⁅Q, Q⁆).map φ := by rw [hmapP]; exact hq
  obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.1 this
  have hker : p⁻¹ * q ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpq]
    group
  have := (⁅Q, Q⁆).mul_mem hp (hZ hker)
  simpa using this

theorem exists_induced {H K : Type} [Group H] [Group K] (ψ : H →* K) (σ : H →* Equiv.Perm (Fin 6))
    (hker : ψ.ker ≤ σ.ker) :
    ∃ φ : ψ.range →* Equiv.Perm (Fin 6), ∀ n : H, φ (ψ.rangeRestrict n) = σ n := by
  have hker' : ψ.rangeRestrict.ker ≤ σ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  exact ⟨ψ.rangeRestrict.liftOfSurjective ψ.rangeRestrict_surjective ⟨σ, hker'⟩, fun n =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨σ, hker'⟩ n⟩

theorem sigma_eq_one_of_conj {H : Type} [Group H] (σ : H →* Equiv.Perm (Fin 6))
    (hσ : Function.Surjective σ) {w : H} (hw3 : w * w * w = 1)
    (hconj : ∀ n : H, ∃ x ∈ σ.ker, n * w * n⁻¹ = w * x ∨ n * w * n⁻¹ = w⁻¹ * x) : σ w = 1 := by
  have hs3 : σ w * σ w * σ w = 1 := by rw [← map_mul, ← map_mul, hw3, map_one]
  have hnorm : (zpowers (σ w)).Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    obtain ⟨n, rfl⟩ := hσ g
    obtain ⟨x, hx, hn | hn⟩ := hconj n
    · have : σ n * σ w * (σ n)⁻¹ = σ w := by
        rw [← map_inv, ← map_mul, ← map_mul, hn, map_mul, MonoidHom.mem_ker.1 hx, mul_one]
      rw [show σ n * σ w ^ k * (σ n)⁻¹ = (σ n * σ w * (σ n)⁻¹) ^ k by simp [conj_zpow], this]
      exact zpow_mem_zpowers _ _
    · have : σ n * σ w * (σ n)⁻¹ = (σ w)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, hn, map_mul, MonoidHom.mem_ker.1 hx, mul_one,
          map_inv]
      rw [show σ n * σ w ^ k * (σ n)⁻¹ = (σ n * σ w * (σ n)⁻¹) ^ k by simp [conj_zpow], this]
      exact (zpowers (σ w)).zpow_mem ((zpowers (σ w)).inv_mem (mem_zpowers _)) k
  have hodd : Odd (Nat.card (zpowers (σ w))) := by
    rw [Nat.card_zpowers]
    exact Odd.of_dvd_nat (by decide : Odd 3)
      (orderOf_dvd_of_pow_eq_one (by rw [pow_three']; exact hs3))
  have := perm6_normal_odd _ hnorm hodd
  have hmem : σ w ∈ zpowers (σ w) := mem_zpowers _
  rw [this] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem mem_alt6_of_cube {x : Equiv.Perm (Fin 6)} (hx : x * x * x = 1) :
    x ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h := congrArg Equiv.Perm.sign hx
  rw [map_mul, map_mul, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem A_le_egNL (h : CSide.Setup L A C z) : A ≤ egNL L A := fun _ ha =>
  mem_inf.2 ⟨le_normalizer ha, h.hAL ha⟩

theorem card_range_psi (h : CSide.Setup L A C z) (hcard : Nat.card (egNL L A) = 138240) :
    Nat.card (CSide.psi h).range = 2160 := by
  have h1 := Subgroup.card_ker_mul_card_range (CSide.psi h)
  have h2 : Nat.card (CSide.psi h).ker = 64 := by
    rw [CSide.ker_psi h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A_le_egNL h)).toEquiv]
    exact h.hF.card_A
  rw [h2, hcard] at h1
  omega

theorem fpf_C_of_fpf_A (h : CSide.Setup L A C z) {m : G} (hmL : m ∈ L)
    (hfpf : ∀ a ∈ A, m * a * m⁻¹ = a → a = 1) {c : G} (hc : c ∈ C) (hmc : m * c * m⁻¹ = c) :
    c = 1 := by
  have hmz : m * z = z * m := Quad.comm_z h.hs hmL
  have hzc : z * c * z⁻¹ * c⁻¹ ∈ A := h.hC.comm_z c hc
  have hmzc : m * (z * c * z⁻¹ * c⁻¹) * m⁻¹ = z * c * z⁻¹ * c⁻¹ := by
    have e1 : m * z * m⁻¹ = z := by rw [hmz]; group
    have e2 : m * z⁻¹ * m⁻¹ = z⁻¹ := by
      calc m * z⁻¹ * m⁻¹ = (m * z * m⁻¹)⁻¹ := by group
        _ = z⁻¹ := by rw [e1]
    have e3 : m * c⁻¹ * m⁻¹ = c⁻¹ := by
      calc m * c⁻¹ * m⁻¹ = (m * c * m⁻¹)⁻¹ := by group
        _ = c⁻¹ := by rw [hmc]
    calc m * (z * c * z⁻¹ * c⁻¹) * m⁻¹
        = (m * z * m⁻¹) * (m * c * m⁻¹) * (m * z⁻¹ * m⁻¹) * (m * c⁻¹ * m⁻¹) := by group
      _ = z * c * z⁻¹ * c⁻¹ := by rw [e1, hmc, e2, e3]
  have h1 : z * c * z⁻¹ * c⁻¹ = 1 := hfpf _ hzc hmzc
  have hcz : c * z = z * c := by
    have : z * c = c * z := by
      calc z * c = (z * c * z⁻¹ * c⁻¹) * (c * z) := by group
        _ = c * z := by rw [h1, one_mul]
    exact this.symm
  exact hfpf c (CSide.mem_A_of_comm h hc hcz) hmc

theorem cyhyp_of_setup
    (h : CSide.Setup L A C z) (hst : SextetType L A) :
    ∃ φ : (CSide.psi h).range →* Equiv.Perm (Fin 6),
      CYHyp (CSide.zt h) (CSide.psi h).range φ ∧
      (∃ α ∈ K0 φ, ∃ β ∈ K0 φ, α * α * α = 1 ∧ β * β * β = 1 ∧ ⁅α, β⁆ ∈ Zk φ ∧ ⁅α, β⁆ ≠ 1) ∧
      (∀ m : egNL L A, CSide.psi h m ∈ Zk φ → CSide.psi h m ≠ 1 →
        ∀ c ∈ C, (m : G) * c * (m : G)⁻¹ = c → c = 1) := by
  classical
  obtain ⟨hcard, σ, hσ, hA, hk, -, -, -⟩ := sym6Index_of_type hst
  obtain ⟨w, a, b, hwN, haN, hbN, hw3, ha3, hb3, hwfix, hwconj, x, hxA, hab⟩ :=
    DResH.sext3a6_of_type hst
  have hAle := A_le_egNL h
  set ψ := CSide.psi h with hψ
  have hkerψ : ψ.ker ≤ σ.ker := by rw [hψ, CSide.ker_psi h]; exact hA
  obtain ⟨φ, hφ⟩ := exists_induced ψ σ hkerψ
  set w' : egNL L A := ⟨w, hwN⟩ with hw'
  set a' : egNL L A := ⟨a, haN⟩ with ha'
  set b' : egNL L A := ⟨b, hbN⟩ with hb'
  have hw'3 : w' * w' * w' = 1 := Subtype.ext hw3
  have ha'3 : a' * a' * a' = 1 := Subtype.ext ha3
  have hb'3 : b' * b' * b' = 1 := Subtype.ext hb3
  have hσw : σ w' = 1 := by
    refine sigma_eq_one_of_conj σ hσ hw'3 fun n => ?_
    obtain ⟨y, hy, hn | hn⟩ := hwconj n n.2
    · exact ⟨⟨y, hAle hy⟩, hA (mem_subgroupOf.2 hy), Or.inl (Subtype.ext hn)⟩
    · exact ⟨⟨y, hAle hy⟩, hA (mem_subgroupOf.2 hy), Or.inr (Subtype.ext hn)⟩
  have hψw : ψ w' ≠ 1 := by
    intro h1
    have hwA : w ∈ A := by
      have : w' ∈ ψ.ker := h1
      rw [hψ, CSide.ker_psi h] at this
      exact mem_subgroupOf.1 this
    have hne : A ≠ ⊥ := by
      intro hbot
      have := h.hF.card_A
      rw [hbot, Subgroup.card_bot] at this
      omega
    obtain ⟨a0, ha0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    apply ha0
    apply Subtype.ext
    refine hwfix a0 a0.2 ?_
    have := h.hF.elem.1 w hwA a0 a0.2
    calc w * (a0 : G) * w⁻¹ = (a0 : G) * w * w⁻¹ := by rw [this]
      _ = a0 := by group
  have hφsurj : Function.Surjective φ := fun y => by
    obtain ⟨n, hn⟩ := hσ y
    exact ⟨ψ.rangeRestrict n, by rw [hφ, hn]⟩
  have hcardK : Nat.card ψ.range = 2160 := card_range_psi h hcard
  have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hkerφ : Nat.card φ.ker = 3 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.2 hφsurj, Subgroup.card_top, h6, hcardK] at h1
    omega
  obtain ⟨x', hx'A, hcomm⟩ : ∃ x' : egNL L A, x' ∈ A.subgroupOf (egNL L A) ∧
      (⁅a', b'⁆ = w' * x' ∨ ⁅a', b'⁆ = w'⁻¹ * x') := by
    refine ⟨⟨x, hAle hxA⟩, mem_subgroupOf.2 hxA, ?_⟩
    rcases hab with hab | hab
    · exact Or.inl (Subtype.ext hab)
    · exact Or.inr (Subtype.ext hab)
  have hψx' : ψ x' = 1 := by
    have : x' ∈ ψ.ker := by rw [hψ, CSide.ker_psi h]; exact hx'A
    exact this
  have hσx' : σ x' = 1 := hA hx'A
  have hσab : σ ⁅a', b'⁆ = 1 := by
    rcases hcomm with hc | hc <;> rw [hc, map_mul]
    · rw [hσw, hσx', mul_one]
    · rw [map_inv, hσw, hσx', inv_one, mul_one]
  have hψab : ψ ⁅a', b'⁆ ≠ 1 := by
    rcases hcomm with hc | hc <;> rw [hc, map_mul, hψx', mul_one]
    · exact hψw
    · rw [map_inv]
      exact inv_ne_one.2 hψw
  have hφa : φ (ψ.rangeRestrict a') ∈ alternatingGroup (Fin 6) := by
    rw [hφ]
    exact mem_alt6_of_cube (by rw [← map_mul, ← map_mul, ha'3, map_one])
  have hφb : φ (ψ.rangeRestrict b') ∈ alternatingGroup (Fin 6) := by
    rw [hφ]
    exact mem_alt6_of_cube (by rw [← map_mul, ← map_mul, hb'3, map_one])
  have hkerab : ⁅ψ.rangeRestrict a', ψ.rangeRestrict b'⁆ ∈ φ.ker := by
    rw [← map_commutatorElement, MonoidHom.mem_ker, hφ]
    exact hσab
  have hneab : ⁅ψ.rangeRestrict a', ψ.rangeRestrict b'⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    intro h1
    exact hψab (congrArg Subtype.val h1)
  have hY : CYHyp (CSide.zt h) ψ.range φ :=
    { order := CSide.orderOf_zt h
      cent := CSide.centralizer_quot_eq h
      comm := by
        rintro _ ⟨y, rfl⟩
        exact CSide.psi_comm h y
      not_mem := CSide.zt_not_mem_range h
      surj := hφsurj
      card_ker := hkerφ
      perfect := perfect_comap_alt6 φ hφsurj hkerφ hφa hφb hkerab hneab }
  refine ⟨φ, hY, ?_, ?_⟩
  · refine ⟨ψ a', mem_K0.2 ⟨ψ.rangeRestrict a', hφa, rfl⟩, ψ b',
      mem_K0.2 ⟨ψ.rangeRestrict b', hφb, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, ha'3, map_one]
    · rw [← map_mul, ← map_mul, hb'3, map_one]
    · rw [← map_commutatorElement]
      exact mem_Zk.2 ⟨ψ.rangeRestrict ⁅a', b'⁆, by rw [hφ]; exact hσab, rfl⟩
    · rw [← map_commutatorElement]
      exact hψab
  · intro m hmZ hm1 c hc hmc
    have hψwZ : ψ w' ∈ Zk φ := mem_Zk.2 ⟨ψ.rangeRestrict w', by rw [hφ]; exact hσw, rfl⟩
    have hfpfA : ∀ y ∈ A, (m : G) * y * (m : G)⁻¹ = y → y = 1 := by
      rcases DResH.LevelC.eq_one_or_eq_or_eq_inv_of_card_three hY.card_Zk hψwZ hψw hmZ with
        h1 | h1 | h1
      · exact absurd h1 hm1
      · have hker : w'⁻¹ * m ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← h1, inv_mul_cancel]
        rw [hψ, CSide.ker_psi h] at hker
        have hyA : w⁻¹ * (m : G) ∈ A := mem_subgroupOf.1 hker
        intro a ha hma
        apply hwfix a ha
        have hya : (w⁻¹ * (m : G)) * a * (w⁻¹ * (m : G))⁻¹ = a := by
          have := h.hF.elem.1 _ hyA a ha
          calc (w⁻¹ * (m : G)) * a * (w⁻¹ * (m : G))⁻¹
              = (a * (w⁻¹ * (m : G))) * (w⁻¹ * (m : G))⁻¹ := by rw [this]
            _ = a := by group
        calc w * a * w⁻¹ = w * ((w⁻¹ * (m : G)) * a * (w⁻¹ * (m : G))⁻¹) * w⁻¹ := by rw [hya]
          _ = (m : G) * a * (m : G)⁻¹ := by group
          _ = a := hma
      · have hker : w' * m ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, h1, mul_inv_cancel]
        rw [hψ, CSide.ker_psi h] at hker
        have hyA : w * (m : G) ∈ A := mem_subgroupOf.1 hker
        intro a ha hma
        apply hwfix a ha
        have hya : (w * (m : G)) * a * (w * (m : G))⁻¹ = a := by
          have := h.hF.elem.1 _ hyA a ha
          calc (w * (m : G)) * a * (w * (m : G))⁻¹
              = (a * (w * (m : G))) * (w * (m : G))⁻¹ := by rw [this]
            _ = a := by group
        have h2 : w⁻¹ * a * w = a := by
          calc w⁻¹ * a * w = w⁻¹ * ((w * (m : G)) * a * (w * (m : G))⁻¹) * w := by rw [hya]
            _ = (m : G) * a * (m : G)⁻¹ := by group
            _ = a := hma
        calc w * a * w⁻¹ = w * (w⁻¹ * a * w) * w⁻¹ := by rw [h2]
          _ = a := by group
    exact fpf_C_of_fpf_A h (mem_inf.1 m.2).2 hfpfA hc hmc

end Concrete

end CFSG.EvenSporadicStandard.M24Std.DRes
