module

public import CFSG.GH74.Generic.BProg.B3.S3FusionII
public import CFSG.GH74.KGroups.L3EpsInvLin

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5
  CFSG.GH74.Generic.BProg.B1.PilotS3 CFSG.GH74.KGroups.L3Eps Subgroup
open scoped commutatorElement

structure SData (X : Type) [Group X] (Kb : Subgroup X) (u : X) (SX : Subgroup X) : Prop where
  perf : ⁅SX, SX⁆ = SX
  le_Kb : SX ≤ Kb
  mem : u ∈ SX
  comm : ∀ s ∈ SX, s * u = u * s
  max : ∀ P : Subgroup X, ⁅P, P⁆ = P → P ≤ Kb → (∀ p ∈ P, p * u = u * p) → P ≤ SX
  comm_mem : ∀ a ∈ Kb, ∀ b ∈ Kb, a * u = u * a → b * u = u * b → ⁅a, b⁆ ∈ SX
  norm : ∀ g : X, g * u = u * g → ∀ s ∈ SX, g * s * g⁻¹ ∈ SX
  inv : ∀ s ∈ SX, s * s = 1 → s = 1 ∨ s = u
  normal_quasi : ∀ A : Subgroup X, A ≤ SX → (∀ a ∈ A, ∀ s ∈ SX, s * a * s⁻¹ ∈ A) →
    (∀ a ∈ A, ∀ s ∈ SX, a * s = s * a) ∨ SX ≤ A
  odd_normal : ∀ A : Subgroup X, A ≤ SX → (∀ a ∈ A, ∀ s ∈ SX, s * a * s⁻¹ ∈ A) →
    (∀ a ∈ A, Odd (orderOf a)) → ∀ a ∈ A, a = 1
  aut : ∀ g : X, g * g = 1 → g * u = u * g → (∀ s ∈ SX, g * s = s * g) →
    (∀ k ∈ Kb, g * k = k * g) ∨ (∀ k ∈ Kb, g * k * g⁻¹ = u * k * u⁻¹)

theorem normal_le_center_or_eq_top' {Q : Type*} [Group Q] (hq : IsQuasisimple Q) (N : Subgroup Q)
    [N.Normal] : N ≤ center Q ∨ N = ⊤ := by
  let quotient := QuotientGroup.mk' (center Q)
  have : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ (QuotientGroup.mk' (center Q)).ker := N.map_eq_bot_iff.mp hbot
    rwa [QuotientGroup.ker_mk'] at hkernel
  · right
    have hsup : N ⊔ center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : _root_.commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hq.1.commutator_eq_top] at hderived
    exact top_unique hderived

theorem SData.of_invData {X : Type} [Group X] [Finite X] {Kb : Subgroup X} (hKb : Kb.Normal) {u : X}
    (hu : u ∈ Kb) (hu2 : u * u = 1) (hu1 : u ≠ 1) {q : ℕ} {S : Subgroup ↥Kb}
    (hS : InvData q ↥Kb ⟨u, hu⟩ S) : SData X Kb u (S.map Kb.subtype) := by
  classical
  have : Kb.Normal := hKb
  set t₀ : ↥Kb := ⟨u, hu⟩ with ht₀
  set SX : Subgroup X := S.map Kb.subtype with hSX
  have hSXKb : SX ≤ Kb := Subgroup.map_subtype_le S
  have hSperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.1 hS.quasisimple.1
  have hperf : ⁅SX, SX⁆ = SX := by rw [hSX, ← Subgroup.map_commutator, hSperf]
  have hcomm : ∀ s ∈ SX, s * u = u * s := by
    rintro _ ⟨s', hs', rfl⟩
    have := mem_centralizer_singleton_iff.mp (hS.le_centralizer hs')
    exact congrArg Subtype.val this
  have hmax : ∀ P : Subgroup X, ⁅P, P⁆ = P → P ≤ Kb → (∀ p ∈ P, p * u = u * p) → P ≤ SX := by
    intro P hP hPK hPc
    set P' : Subgroup ↥Kb := P.comap Kb.subtype with hP'
    have hmap : P'.map Kb.subtype = P := by
      rw [hP']
      exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
    have hP'perf : ⁅P', P'⁆ = P' := by
      apply Subgroup.map_injective Kb.subtype_injective
      rw [Subgroup.map_commutator, hmap]
      exact hP
    have hP'le : P' ≤ S := by
      rw [← hP'perf]
      refine Subgroup.commutator_le.mpr fun a ha b hb => hS.commutator_mem a ?_ b ?_
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext (hPc _ ha))
      · exact mem_centralizer_singleton_iff.mpr (Subtype.ext (hPc _ hb))
    calc P = P'.map Kb.subtype := hmap.symm
      _ ≤ S.map Kb.subtype := Subgroup.map_mono hP'le
  refine ⟨hperf, hSXKb, ⟨t₀, hS.mem, rfl⟩, hcomm, hmax, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hau hbu
    have hmem := hS.commutator_mem ⟨a, ha⟩ (mem_centralizer_singleton_iff.mpr (Subtype.ext hau))
      ⟨b, hb⟩ (mem_centralizer_singleton_iff.mpr (Subtype.ext hbu))
    exact ⟨_, hmem, by simp [commutatorElement_def]⟩
  · intro g hg s hs
    have hP : ⁅SX.map (MulAut.conj g).toMonoidHom, SX.map (MulAut.conj g).toMonoidHom⁆ =
        SX.map (MulAut.conj g).toMonoidHom := by rw [← Subgroup.map_commutator, hperf]
    have hle := hmax _ hP (by
      rintro _ ⟨s', hs', rfl⟩
      exact hKb.conj_mem s' (hSXKb hs') g) (by
      rintro _ ⟨s', hs', rfl⟩
      have := hcomm s' hs'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * s' * g⁻¹ * u = g * (s' * u) * g⁻¹ := by
            calc g * s' * g⁻¹ * u = g * s' * (g⁻¹ * u) := by group
              _ = g * s' * (u * g⁻¹) := by
                have : g⁻¹ * u = u * g⁻¹ := by
                  calc g⁻¹ * u = g⁻¹ * (u * g) * g⁻¹ := by group
                    _ = g⁻¹ * (g * u) * g⁻¹ := by rw [hg]
                    _ = u * g⁻¹ := by group
                rw [this]
              _ = g * (s' * u) * g⁻¹ := by group
        _ = g * (u * s') * g⁻¹ := by rw [this]
        _ = u * (g * s' * g⁻¹) := by
            calc g * (u * s') * g⁻¹ = (g * u * g⁻¹) * (g * s' * g⁻¹) := by group
              _ = u * (g * s' * g⁻¹) := by
                have : g * u * g⁻¹ = u := by rw [hg]; group
                rw [this])
    exact hle ⟨s, hs, rfl⟩
  · intro s hs hs2
    obtain ⟨s', hs', rfl⟩ := hs
    have := hS.involution s' hs' (Subtype.ext hs2)
    rcases this with h | h
    · left; rw [h]; rfl
    · right; rw [h]; exact rfl
  · intro A hAS hA
    let A' : Subgroup ↥S := A.comap (Kb.subtype.comp S.subtype)
    have hA'n : A'.Normal := ⟨fun a ha s => by
      show ((s * a * s⁻¹ : ↥S) : X) ∈ A
      simpa using hA _ ha ((s : ↥Kb) : X) ⟨(s : ↥Kb), s.2, rfl⟩⟩
    rcases normal_le_center_or_eq_top' hS.quasisimple A' with hc | htop
    · left
      intro a ha s hs
      obtain ⟨s', hs', rfl⟩ := hs
      have haSX := hAS ha
      obtain ⟨a', ha', rfl⟩ := haSX
      have : (⟨a', ha'⟩ : ↥S) ∈ A' := ha
      have := Subgroup.mem_center_iff.mp (hc this) ⟨s', hs'⟩
      exact congrArg (fun z : ↥S => ((z : ↥Kb) : X)) this.symm
    · right
      rintro _ ⟨s', hs', rfl⟩
      have : (⟨s', hs'⟩ : ↥S) ∈ A' := by rw [htop]; exact Subgroup.mem_top _
      exact this
  · intro A hAS hA hodd a ha
    let A' : Subgroup ↥S := A.comap (Kb.subtype.comp S.subtype)
    have hA'n : A'.Normal := ⟨fun a ha s => by
      show ((s * a * s⁻¹ : ↥S) : X) ∈ A
      simpa using hA _ ha ((s : ↥Kb) : X) ⟨(s : ↥Kb), s.2, rfl⟩⟩
    obtain ⟨a', ha', rfl⟩ := hAS ha
    have haA' : (⟨a', ha'⟩ : ↥S) ∈ A' := ha
    have hu_ord : ¬ Odd (orderOf u) := by
      have : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
      rw [this]
      decide
    have htS : t₀ ∈ S := hS.mem
    rcases normal_le_center_or_eq_top' hS.quasisimple A' with hc | htop
    · have h' : a' = 1 ∨ a' = t₀ := hS.center ⟨a', ha'⟩ (hc haA')
      rcases h' with h | h
      · rw [h]; rfl
      · exfalso
        apply hu_ord
        have h2 := hodd _ ha
        rwa [show (Kb.subtype a' : X) = u by rw [h]; rfl] at h2
    · exfalso
      apply hu_ord
      have : (⟨t₀, htS⟩ : ↥S) ∈ A' := by rw [htop]; exact Subgroup.mem_top _
      exact hodd _ this
  · intro g hg2 hgu hgS
    let σ : MulAut ↥Kb := MulAut.conjNormal g
    have hσ_apply : ∀ k : ↥Kb, ((σ k : ↥Kb) : X) = g * k * g⁻¹ := fun k => MulAut.conjNormal_apply g k
    have hσ2 : σ * σ = 1 := by
      have : σ * σ = MulAut.conjNormal (g * g) := (map_mul MulAut.conjNormal g g).symm
      rw [this, hg2, map_one]
    have hfix : ∀ s ∈ S, σ s = s := by
      intro s hs
      apply Subtype.ext
      rw [hσ_apply]
      have := hgS (s : X) ⟨s, hs, rfl⟩
      calc g * (s : X) * g⁻¹ = ((s : X) * g) * g⁻¹ := by rw [this]
        _ = s := by group
    rcases hS.aut_fixing σ hσ2 hfix with h1 | h1
    · left
      intro k hk
      have := congrArg (fun τ : MulAut ↥Kb => ((τ ⟨k, hk⟩ : ↥Kb) : X)) h1
      simp only [hσ_apply, MulAut.one_apply] at this
      calc g * k = (g * k * g⁻¹) * g := by group
        _ = k * g := by rw [this]
    · right
      intro k hk
      have := congrArg (fun τ : MulAut ↥Kb => ((τ ⟨k, hk⟩ : ↥Kb) : X)) h1
      simp only [hσ_apply, MulAut.conj_apply] at this
      exact this

section Swap

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Th_le_C (x y : G) : Th x y ≤ centralizer ({x} : Set G) := (maxPerfect_le _).trans inf_le_left

noncomputable def f0 (x y : G) : ↥(Th x y) →* CentralizerBar x :=
  (proj x).comp (Subgroup.inclusion (Th_le_C x y))

omit [Finite G] in
theorem f0_apply (x y : G) (θ : ↥(Th x y)) : f0 x y θ = piC x (θ : G) :=
  (piC_of_mem x (Th_le_C x y θ.2)).symm

omit [Finite G] in
theorem mem_range_f0 {x y : G} {l : CentralizerBar x} :
    l ∈ (f0 x y).range ↔ ∃ θ ∈ Th x y, piC x θ = l := by
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ, θ.2, (f0_apply x y θ).symm⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨⟨θ, hθ⟩, f0_apply x y ⟨θ, hθ⟩⟩

omit [Finite G] in
theorem imgBar_Th_eq_range (x y : G) : S3.imgBar x (Th x y) = (f0 x y).range := by
  ext c
  rw [mem_imgBar, mem_range_f0]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, piC_of_mem x g.2⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨⟨θ, Th_le_C x y hθ⟩, hθ, (piC_of_mem x _).symm⟩

theorem ker_f0_le_Q (x y : G) : (f0 x y).ker ≤ pPrimeCore 2 ↥(Th x y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ θ ∈ (f0 x y).ker, Odd (orderOf θ) := by
    intro θ hθ
    have h1 : proj x (Subgroup.inclusion (Th_le_C x y) θ) = 1 := hθ
    have := proj_odd x (Subgroup.inclusion (Th_le_C x y) θ) h1
    have e := orderOf_injective (Subgroup.inclusion (Th_le_C x y))
      (Subgroup.inclusion_injective (Th_le_C x y)) θ
    rwa [e] at this
  have hcop : Nat.Coprime 2 (Nat.card ↥(f0 x y).ker) := by
    rw [Nat.coprime_two_left]
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥(f0 x y).ker := by
      rcases Nat.even_or_odd (Nat.card ↥(f0 x y).ker) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hne
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(f0 x y).ker) 2 h2
    have := hodd (z : ↥(Th x y)) z.2
    rw [Subgroup.orderOf_coe, hz] at this
    exact absurd this (by decide)
  exact le_sSup ⟨inferInstance, hcop⟩

end Swap

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
