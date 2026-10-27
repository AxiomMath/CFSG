module

public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Pure

open scoped commutatorElement

namespace GrpAux

theorem mem_sup_of_comm {K : Type*} [Group K] {P Q : Subgroup K}
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {z : K} (hz : z ∈ P ⊔ Q) :
    ∃ x ∈ P, ∃ y ∈ Q, z = x * y := by
  let T : Subgroup K :=
    { carrier := {z | ∃ x ∈ P, ∃ y ∈ Q, z = x * y}
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', P.mul_mem hx hx', y * y', Q.mul_mem hy hy', ?_⟩
        have h := hc x' hx' y hy
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [← h]
          _ = x * x' * (y * y') := by group
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, P.inv_mem hx, y⁻¹, Q.inv_mem hy, ?_⟩
        have h := hc x⁻¹ (P.inv_mem hx) y⁻¹ (Q.inv_mem hy)
        calc (x * y)⁻¹ = y⁻¹ * x⁻¹ := by group
          _ = x⁻¹ * y⁻¹ := h.symm }
  have hP : P ≤ T := fun x hx => ⟨x, hx, 1, Q.one_mem, by simp⟩
  have hQ : Q ≤ T := fun y hy => ⟨1, P.one_mem, y, hy, by simp⟩
  exact (sup_le hP hQ) hz

theorem normal_le_center_or_eq_top {G : Type*} [Group G] (hq : CFSG.Open.IsQuasisimple G)
    (N : Subgroup G) [hN : N.Normal] : N ≤ Subgroup.center G ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hq
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center G))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center G))) with
    h | h
  · left
    intro n hn
    have hmem : QuotientGroup.mk' (Subgroup.center G) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center G)) := Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff n).1 hmem
  · right
    have hcomm : commutator G ≤ N := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
      have hg₁ : QuotientGroup.mk' (Subgroup.center G) g₁ ∈
          N.map (QuotientGroup.mk' (Subgroup.center G)) := by
        rw [h]
        trivial
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.1 hg₁
      have hz : n⁻¹ * g₁ ∈ Subgroup.center G := QuotientGroup.eq.1 hng
      have hzg : (n⁻¹ * g₁) * g₂ = g₂ * (n⁻¹ * g₁) := (Subgroup.mem_center_iff.1 hz g₂).symm
      have hcomm' : ⁅g₁, g₂⁆ = n * (g₂ * n⁻¹ * g₂⁻¹) := by
        have hg : g₁ = n * (n⁻¹ * g₁) := by group
        rw [commutatorElement_def]
        conv_lhs => rw [hg]
        calc n * (n⁻¹ * g₁) * g₂ * (n * (n⁻¹ * g₁))⁻¹ * g₂⁻¹
            = n * ((n⁻¹ * g₁) * g₂) * (n⁻¹ * g₁)⁻¹ * n⁻¹ * g₂⁻¹ := by group
          _ = n * (g₂ * (n⁻¹ * g₁)) * (n⁻¹ * g₁)⁻¹ * n⁻¹ * g₂⁻¹ := by rw [hzg]
          _ = n * (g₂ * n⁻¹ * g₂⁻¹) := by group
      rw [hcomm']
      exact N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) _)
    rw [eq_top_iff, ← hperf]
    exact hcomm

theorem mem_of_le_zpowers {K : Type*} [Group K] [Finite K] {k : K} (hk3 : orderOf k = 3)
    {S : Subgroup K} (hS : S ≤ Subgroup.zpowers k) (hne : S ≠ ⊥) : k ∈ S := by
  have hcard : Nat.card (Subgroup.zpowers k) = 3 := by rw [Nat.card_zpowers, hk3]
  have hdvd : Nat.card S ∣ 3 := hcard ▸ Subgroup.card_dvd_of_le hS
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq S h1) hne
  · have hS' : S = Subgroup.zpowers k :=
      Subgroup.eq_of_le_of_card_ge hS (by rw [hcard, h3])
    rw [hS']
    exact Subgroup.mem_zpowers k

theorem mem_ker_iff_mem_centralizer {K : Type*} [Group K] {C H : Subgroup K}
    (f : ↥H →* MulAut ↥C)
    (hf : ∀ (h : ↥H) (c : ↥C), ((f h c : ↥C) : K) = (h : K) * c * (h : K)⁻¹) (h : ↥H) :
    h ∈ f.ker ↔ (h : K) ∈ Subgroup.centralizer (C : Set K) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 c hc
    have h2 := congrArg (fun α : MulAut ↥C => ((α ⟨c, hc⟩ : ↥C) : K)) h1
    simp only [hf, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro h1
    ext c
    rw [hf, MulAut.one_apply]
    exact mul_inv_eq_of_eq_mul (h1 c c.2).symm

theorem mem_centralizer_of_le_sup {K : Type*} [Group K] [Finite K] (C D J : Subgroup K) (k : K)
    (n : ℕ) (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) (hJle : J ≤ C ⊔ D)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hkJ : k ∈ J) (hk3 : orderOf k = 3)
    (hZJ : ∀ z ∈ J, z ∈ Subgroup.centralizer (J : Set K) → z ∈ Subgroup.zpowers k)
    (hJcard : Nat.card ↥J = 3 * n)
    (hCcard : Nat.card ↥C ≤ n * Nat.card ↥(C ⊓ Subgroup.centralizer (C : Set K))) :
    k ∈ Subgroup.centralizer (C : Set K) := by
  have hJN : J ≤ Subgroup.normalizer (C : Set K) := by
    refine hJle.trans (sup_le Subgroup.le_normalizer fun d hd => ?_)
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun c hc => ?_)
    exact hCD c hc d hd
  let φ : ↥J →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hJN)
  have hφ : ∀ (j : ↥J) (c : ↥C), ((φ j c : ↥C) : K) = (j : K) * c * (j : K)⁻¹ := by
    intro j c
    simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  let ψ : ↥C →* MulAut ↥C := MulAut.conj
  have hψ : ∀ (c c' : ↥C), ((ψ c c' : ↥C) : K) = (c : K) * c' * (c : K)⁻¹ := by
    intro c c'
    simp [ψ, MulAut.conj_apply]
  have hrange : φ.range ≤ ψ.range := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc, d, hd, hjcd⟩ := mem_sup_of_comm hCD (hJle j.2)
    refine ⟨⟨c, hc⟩, ?_⟩
    ext x
    rw [hψ, hφ, hjcd]
    have hdx : (d : K) * x = x * d := (hCD x x.2 d hd).symm
    calc c * (x : K) * c⁻¹ = c * ((x : K) * d) * d⁻¹ * c⁻¹ := by group
      _ = c * (d * (x : K)) * d⁻¹ * c⁻¹ := by rw [hdx]
      _ = c * d * x * (c * d)⁻¹ := by group
  have hJ : Nat.card ↥J = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  have hC : Nat.card ↥C = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker]
  have hkerψ : ψ.ker = (C ⊓ Subgroup.centralizer (C : Set K)).subgroupOf C := by
    ext c
    rw [mem_ker_iff_mem_centralizer ψ hψ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨c.2, h⟩, fun h => h.2⟩
  have hkerψcard : Nat.card ↥ψ.ker = Nat.card ↥(C ⊓ Subgroup.centralizer (C : Set K)) := by
    rw [hkerψ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrangeCard : Nat.card ↥φ.range ≤ n := by
    have h3 : Nat.card ↥φ.range ≤ Nat.card ↥ψ.range := Subgroup.card_le_of_le hrange
    have hpos : 0 < Nat.card ↥ψ.ker := Nat.card_pos
    have h4 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ Nat.card ↥ψ.ker * n := by
      rw [← hC, hkerψcard, mul_comm]
      exact hCcard
    have h5 := Nat.le_of_mul_le_mul_left h4 hpos
    omega
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  rcases normal_le_center_or_eq_top hJq φ.ker with hle | htop
  ·
    have hS : J ⊓ Subgroup.centralizer (C : Set K) ≤ Subgroup.zpowers k := by
      intro s hs
      obtain ⟨hsJ, hsC⟩ := Subgroup.mem_inf.1 hs
      have hsker : (⟨s, hsJ⟩ : ↥J) ∈ φ.ker := (mem_ker_iff_mem_centralizer φ hφ _).2 hsC
      have hsz := hle hsker
      refine hZJ s hsJ (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hsz ⟨y, hy⟩)
    have hne : J ⊓ Subgroup.centralizer (C : Set K) ≠ ⊥ := by
      intro hbot
      have hker : φ.ker = ⊥ := by
        ext j
        rw [mem_ker_iff_mem_centralizer φ hφ, Subgroup.mem_bot]
        constructor
        · intro hj
          have hjmem : (j : K) ∈ J ⊓ Subgroup.centralizer (C : Set K) :=
            Subgroup.mem_inf.2 ⟨j.2, hj⟩
          rw [hbot, Subgroup.mem_bot] at hjmem
          exact Subtype.ext hjmem
        · rintro rfl
          exact Subgroup.one_mem _
      have hker1 : Nat.card ↥φ.ker = 1 := by
        rw [hker]
        exact Subgroup.card_bot
      rw [hker1, one_mul] at hJ
      have hJpos : 0 < Nat.card ↥J := Nat.card_pos
      omega
    exact (Subgroup.mem_inf.1 (mem_of_le_zpowers hk3 hS hne)).2
  ·
    exact (mem_ker_iff_mem_centralizer φ hφ ⟨k, hkJ⟩).1 (htop ▸ Subgroup.mem_top _)

end GrpAux

theorem key_center {K : Type*} [Group K] [Finite K] (A B J : Subgroup K) (e k : K) (n : ℕ)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hJle : J ≤ A ⊔ B)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hkJ : k ∈ J)
    (hkc : k ∈ Subgroup.centralizer (J : Set K)) (hk3 : orderOf k = 3)
    (hZJ : ∀ z ∈ J, z ∈ Subgroup.centralizer (J : Set K) → z ∈ Subgroup.zpowers k)
    (hJcard : Nat.card ↥J = 3 * n)
    (hAZ : ∀ a ∈ A, a ∈ Subgroup.centralizer (A : Set K) → a ∈ Subgroup.zpowers e)
    (hBZ : ∀ b ∈ B, b ∈ Subgroup.centralizer (B : Set K) → b ∈ Subgroup.zpowers e)
    (hAcard : Nat.card ↥A ≤ n * Nat.card ↥(A ⊓ Subgroup.centralizer (A : Set K)))
    (hBcard : Nat.card ↥B ≤ n * Nat.card ↥(B ⊓ Subgroup.centralizer (B : Set K))) :
    k ∈ Subgroup.zpowers e := by
  have hkA : k ∈ Subgroup.centralizer (A : Set K) :=
    GrpAux.mem_centralizer_of_le_sup A B J k n hAB hJle hJq hkJ hk3 hZJ hJcard hAcard
  have hkB : k ∈ Subgroup.centralizer (B : Set K) :=
    GrpAux.mem_centralizer_of_le_sup B A J k n (fun b hb a ha => (hAB a ha b hb).symm)
      (by rwa [sup_comm] at hJle) hJq hkJ hk3 hZJ hJcard hBcard
  obtain ⟨a, ha, b, hb, hab⟩ := GrpAux.mem_sup_of_comm hAB (hJle hkJ)
  have haZ : a ∈ Subgroup.zpowers e := by
    refine hAZ a ha (Subgroup.mem_centralizer_iff.2 fun a' ha' => ?_)
    have h1 : a' * k = k * a' := Subgroup.mem_centralizer_iff.1 hkA a' ha'
    rw [hab] at h1
    have h2 : a' * b = b * a' := hAB a' ha' b hb
    have h3 : a' * a * b = a * a' * b := by
      calc a' * a * b = a' * (a * b) := by group
        _ = a * b * a' := h1
        _ = a * (b * a') := by group
        _ = a * (a' * b) := by rw [h2]
        _ = a * a' * b := by group
    exact mul_right_cancel h3
  have hbZ : b ∈ Subgroup.zpowers e := by
    refine hBZ b hb (Subgroup.mem_centralizer_iff.2 fun b' hb' => ?_)
    have h1 : b' * k = k * b' := Subgroup.mem_centralizer_iff.1 hkB b' hb'
    rw [hab] at h1
    have h2 : a * b' = b' * a := hAB a ha b' hb'
    have h3 : a * (b' * b) = a * (b * b') := by
      calc a * (b' * b) = a * b' * b := by group
        _ = b' * a * b := by rw [h2]
        _ = b' * (a * b) := by group
        _ = a * b * b' := h1
        _ = a * (b * b') := by group
    exact mul_left_cancel h3
  rw [hab]
  exact Subgroup.mul_mem _ haZ hbZ

theorem relIndex_ge_of_inf_le_zpowers {K : Type*} [Group K] [Finite K] (E J : Subgroup K) (k : K)
    (hk3 : orderOf k = 3)
    (hle : E ⊓ Subgroup.centralizer (J : Set K) ≤ Subgroup.zpowers k) (h27 : 27 ≤ Nat.card ↥E) :
    9 ≤ (Subgroup.centralizer (J : Set K)).relIndex E := by
  have h1 : Nat.card ↥((Subgroup.centralizer (J : Set K)).subgroupOf E) *
      (Subgroup.centralizer (J : Set K)).relIndex E = Nat.card ↥E :=
    Subgroup.card_mul_index _
  have h2 : Nat.card ↥((Subgroup.centralizer (J : Set K)).subgroupOf E) ≤ 3 := by
    have h3 : Nat.card ↥((Subgroup.centralizer (J : Set K)).subgroupOf E) =
        Nat.card ↥(E ⊓ Subgroup.centralizer (J : Set K)) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h3]
    calc Nat.card ↥(E ⊓ Subgroup.centralizer (J : Set K))
        ≤ Nat.card ↥(Subgroup.zpowers k) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, hk3]
  by_contra hlt
  have h4 : (Subgroup.centralizer (J : Set K)).relIndex E ≤ 8 := by omega
  have h5 : Nat.card ↥((Subgroup.centralizer (J : Set K)).subgroupOf E) *
      (Subgroup.centralizer (J : Set K)).relIndex E ≤ 3 * 8 := Nat.mul_le_mul h2 h4
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Pure

end
