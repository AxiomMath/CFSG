module

public import CFSG.GH74.Generic.BProg.B3.S3FusionSD
public import CFSG.GH74.Generic.BProg.B3.S3L3Lift

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3PumpSData

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.Generic.BProg.B1.PilotS3 CFSG.GH74.KGroups.L3Eps
  Subgroup
open scoped commutatorElement

theorem ofInvDataB4 {X : Type} [Group X] [Finite X] {Kb : Subgroup X} (hKb : Kb.Normal) {u : X}
    (hu : u ∈ Kb) (hu2 : u * u = 1) (hu1 : u ≠ 1) {q : ℕ} {S : Subgroup ↥Kb}
    (hS : InvDataB4 q ↥Kb ⟨u, hu⟩ S) : SData X Kb u (S.map Kb.subtype) := by
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
    have hσ_apply : ∀ k : ↥Kb, ((σ k : ↥Kb) : X) = g * k * g⁻¹ := fun k =>
      MulAut.conjNormal_apply g k
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

theorem exists_invDataB4 {Kt : Type} [Group Kt] [Finite Kt] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hX : StatedClassicalModel Kt t 3 p f) {w : Kt} (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ∃ S : Subgroup Kt, InvDataB4 (p ^ f) Kt w S := by
  rcases ht with rfl | rfl
  · exact S3.exists_invDataB4_lin hp hp2 h5 hX hw2 hw1
  · obtain ⟨S, hS⟩ := ((S3.libData_uni hp hp2 h5) Kt hX).1 w hw2 hw1
    exact ⟨S, hS.toB4⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_sdata_layer {x : G} {K : Subgroup G} {y : G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (hyK : y ∈ K) (hy : orderOf y = 2)
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup ↥(S3.imgBar x K)),
      S3L3Lift.LayerHyp x hK.1 hyK S F ∧
        SData (CentralizerBar x) (S3.imgBar x K) (piC x y) (S.map (S3.imgBar x K).subtype) := by
  classical
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := hshape.model
  have hq3 : QShape3 ↥(S3.imgBar x K) := by
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  have hZ : ∀ z : ↥(S3.imgBar x K), (∀ g : ↥(S3.imgBar x K), g * z = z * g) → z = 1 := by
    intro z hz
    have hmem : z ∈ center ↥(S3.imgBar x K) := Subgroup.mem_center_iff.2 fun g => hz g
    rw [hshape.centerless, Subgroup.mem_bot] at hmem
    exact hmem
  have hyo := S3L3Lift.orderOf_yK x hK.1 hyK hy
  obtain ⟨F, hF, hFin, S, hodd, h5', ⟨e⟩, huS, hSle, hcomm, hSpc, hB4⟩ :=
    S3L3KGroup.exists_sl2_component hq3 hZ hyo
  have hX : StatedClassicalModel ↥(S3.imgBar x K) t 3 p f := by
    rcases ht with rfl | rfl
    · exact stated_of_lieModel_PSL hmod
    · exact stated_of_lieModel_PSU hmod
  have hw2 : S3L3Lift.yK x hK.1 hyK * S3L3Lift.yK x hK.1 hyK = 1 := by
    have := pow_orderOf_eq_one (S3L3Lift.yK x hK.1 hyK)
    rwa [hyo, pow_two] at this
  have hw1 : S3L3Lift.yK x hK.1 hyK ≠ 1 := fun h => by
    rw [h, orderOf_one] at hyo
    omega
  obtain ⟨S', hS'⟩ := exists_invDataB4 ht hp hp2 h5 hX hw2 hw1
  have hSq : IsQuasisimple ↥S := isQuasisimple_of_equiv_sl2 (by omega) e
  have hSperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.1 hSq.1
  have hS'perf : ⁅S', S'⁆ = S' := Subgroup.isPerfect_iff.1 hS'.quasisimple.1
  have hSS' : S = S' := by
    apply le_antisymm
    · calc S = ⁅S, S⁆ := hSperf.symm
        _ ≤ S' := Subgroup.commutator_le.2 fun a ha b hb =>
          hS'.commutator_mem a (hSle ha) b (hSle hb)
    · calc S' = ⁅S', S'⁆ := hS'perf.symm
        _ ≤ S := Subgroup.commutator_le.2 fun a ha b hb =>
          hcomm a (hS'.le_centralizer ha) b (hS'.le_centralizer hb)
  subst hSS'
  refine ⟨F, hF, hFin, S, ⟨hodd, by omega, ⟨e⟩, huS, hSpc,
    fun M hM => S3L3Lift.eq_of_isPCompIn_centralizer hSpc hcomm hM⟩, ?_⟩
  exact ofInvDataB4 hshape.normal (S3L3Lift.yK x hK.1 hyK).2 (by
      have := congrArg Subtype.val hw2
      simpa using this) (fun h => hw1 (Subtype.ext h)) hS'

end S3PumpSData

end CFSG.GH74.Generic.BProg.B3
