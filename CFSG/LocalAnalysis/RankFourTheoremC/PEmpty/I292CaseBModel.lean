module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBStab
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBTwoPart
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBTorus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

structure MatModel (p : ℕ) (K : Type) [Field K] (P' : Type) [Group P'] where
  H : Subgroup (GL (Fin p) K)
  𝔾 : Subgroup (GL (Fin p) K)
  norm_mem : ∀ g ∈ 𝔾, ∀ A ∈ H, g * A * g⁻¹ ∈ H
  ι : ↥H →* P'
  c : ↥𝔾 →* MulAut P'
  det_one : ∀ A ∈ H, (A : Matrix (Fin p) (Fin p) K).det = 1
  ι_surj : Function.Surjective ι
  ι_eq_one : ∀ A : ↥H, ι A = 1 ↔
    ∃ z : Kˣ, (A : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) z
  c_ι : ∀ (g : ↥𝔾) (A : ↥H), c g (ι A) =
    ι ⟨(g : GL (Fin p) K) * A * (g : GL (Fin p) K)⁻¹, norm_mem g g.2 A A.2⟩
  c_eq_one : ∀ g : ↥𝔾, c g = 1 → ∃ z : Kˣ, (g : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) z

variable {p : ℕ} {K : Type} [Field K] {P' : Type} [Group P'] (M : MatModel p K P')

@[expose] def MatModel.conjH (g : ↥M.𝔾) (A : ↥M.H) : ↥M.H :=
  ⟨(g : GL (Fin p) K) * A * (g : GL (Fin p) K)⁻¹, M.norm_mem g g.2 A A.2⟩

theorem MatModel.c_ι' (g : ↥M.𝔾) (A : ↥M.H) : M.c g (M.ι A) = M.ι (M.conjH g A) :=
  M.c_ι g A

structure MatModel.IsLift (Tb : Subgroup P') (Th : Subgroup (GL (Fin p) K)) : Prop where
  le_H : Th ≤ M.H
  two : IsPGroup 2 Th
  ne_bot : Th ≠ ⊥
  dec : ∀ A : ↥M.H, M.ι A ∈ Tb → ∃ s ∈ Th, ∃ z : Kˣ,
    (A : GL (Fin p) K) = s * GeneralLinearGroup.scalar (Fin p) z
  mem : ∀ s ∈ Th, ∃ hs : s ∈ M.H, M.ι ⟨s, hs⟩ ∈ Tb
  two_mem : ∀ A : ↥M.H, M.ι A ∈ Tb → (∃ k : ℕ, (A : GL (Fin p) K) ^ (2 ^ k) = 1) →
    (A : GL (Fin p) K) ∈ Th

theorem MatModel.exists_isLift [Finite K] {Tb : Subgroup P'}
    (hT2 : ∀ t ∈ Tb, ∃ k : ℕ, t ^ (2 ^ k) = 1) (hTne : Tb ≠ ⊥) :
    ∃ Th : Subgroup (GL (Fin p) K), M.IsLift Tb Th := by
  classical
  set Γ : Subgroup ↥M.H := Tb.comap M.ι with hΓ
  set π : ↥Γ →* P' := M.ι.comp Γ.subtype with hπ
  have hker : π.ker ≤ center ↥Γ := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    obtain ⟨z, hz⟩ := (M.ι_eq_one (A : ↥M.H)).1 hA
    rw [Subgroup.mem_center_iff]
    intro B
    apply Subtype.ext
    apply Subtype.ext
    change (B : GL (Fin p) K) * ((A : ↥M.H) : GL (Fin p) K) =
      ((A : ↥M.H) : GL (Fin p) K) * (B : GL (Fin p) K)
    rw [hz]
    exact (scalar_comm z _).symm
  have h2 : ∀ d ∈ π.range, ∃ k : ℕ, d ^ (2 ^ k) = 1 := by
    rintro _ ⟨A, rfl⟩
    exact hT2 _ A.2
  obtain ⟨S, hSn, hS2, hSmem, hSdec⟩ := exists_twoPart π hker h2
  set emb : ↥Γ →* GL (Fin p) K := M.H.subtype.comp Γ.subtype with hemb
  have hembinj : Function.Injective emb := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  refine ⟨S.map emb, ⟨?_, hS2.map emb, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨s, -, rfl⟩
    exact (s : ↥M.H).2
  · obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hTne
    obtain ⟨A, hA⟩ := M.ι_surj t
    have hAΓ : A ∈ Γ := by
      show M.ι A ∈ Tb
      rw [hA]
      exact ht
    obtain ⟨s, hs, z, hz, hsz⟩ := hSdec ⟨A, hAΓ⟩
    have hz1 : M.ι (z : ↥M.H) = 1 := MonoidHom.mem_ker.1 hz
    have h1 : M.ι A = M.ι (s : ↥M.H) := by
      have : (⟨A, hAΓ⟩ : ↥Γ) = s * z := hsz
      have h2 := congrArg (fun x : ↥Γ => M.ι (x : ↥M.H)) this
      simp only [Subgroup.coe_mul, map_mul, hz1, mul_one] at h2
      exact h2
    intro hbot
    have hmem : emb s ∈ S.map emb := ⟨s, hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : s = 1 := hembinj (by rw [hmem, map_one])
    apply ht1
    have : t = 1 := by
      rw [← hA, h1, this]
      simp
    exact Subtype.ext this
  · intro A hA
    obtain ⟨s, hs, z, hz, hsz⟩ := hSdec ⟨A, hA⟩
    refine ⟨emb s, ⟨s, hs, rfl⟩, ?_⟩
    obtain ⟨c, hc⟩ := (M.ι_eq_one ((z : ↥Γ) : ↥M.H)).1 (MonoidHom.mem_ker.1 hz)
    refine ⟨c, ?_⟩
    have : (⟨A, hA⟩ : ↥Γ) = s * z := hsz
    have h2 := congrArg emb this
    rw [map_mul] at h2
    have h3 : emb z = GeneralLinearGroup.scalar (Fin p) c := hc
    rw [h3] at h2
    exact h2
  · rintro _ ⟨s, -, rfl⟩
    exact ⟨(s : ↥M.H).2, s.2⟩
  · intro A hA hk
    obtain ⟨k, hk⟩ := hk
    have hA2 : (⟨A, hA⟩ : ↥Γ) ∈ S := by
      refine hSmem _ ⟨k, ?_⟩
      exact Subtype.ext (Subtype.ext (by simpa using hk))
    exact ⟨⟨A, hA⟩, hA2, rfl⟩

section Interface

variable {M} {Tb : Subgroup P'} {Th : Subgroup (GL (Fin p) K)}

theorem scalar_eq_one {z : Kˣ} (hp : p ≠ 0)
    (h : GeneralLinearGroup.scalar (Fin p) z = (1 : GL (Fin p) K)) : z = 1 := by
  have := congrArg (fun x : GL (Fin p) K =>
    (x : Matrix (Fin p) (Fin p) K) ⟨0, Nat.pos_of_ne_zero hp⟩ ⟨0, Nat.pos_of_ne_zero hp⟩) h
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem MatModel.scalar_pow_eq_one {z : Kˣ}
    (hz : (GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) ∈ M.H) : z ^ p = 1 := by
  have h1 := M.det_one _ hz
  rw [det_scalar_eq] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, h1, Units.val_one]

theorem MatModel.IsLift.conj_mem (hL : M.IsLift Tb Th) {g : ↥M.𝔾} (hg : M.c g ∈ stabSub Tb)
    {s : GL (Fin p) K} (hs : s ∈ Th) : (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ ∈ Th := by
  obtain ⟨hsH, hsT⟩ := hL.mem s hs
  have h1 : M.ι (M.conjH g ⟨s, hsH⟩) ∈ Tb := by
    rw [← M.c_ι' g ⟨s, hsH⟩]
    exact (mem_stabSub.1 hg _).1 hsT
  have h2 : ∃ k : ℕ, (((M.conjH g ⟨s, hsH⟩ : ↥M.H)) : GL (Fin p) K) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hL.two ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    change ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹) ^ (2 ^ k) = 1
    rw [conj_pow, hk']
    group
  exact hL.two_mem _ h1 h2

theorem MatModel.IsLift.mem_normalizer_of_stab (hL : M.IsLift Tb Th) {g : ↥M.𝔾}
    (hg : M.c g ∈ stabSub Tb) : (g : GL (Fin p) K) ∈ normalizer (Th : Set (GL (Fin p) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => hL.conj_mem hg hs, fun hs => ?_⟩
  have hg' : M.c g⁻¹ ∈ stabSub Tb := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hg
  have := hL.conj_mem hg' hs
  simpa [mul_assoc] using this

theorem MatModel.IsLift.stab_of_mem_normalizer (hL : M.IsLift Tb Th) {g : ↥M.𝔾}
    (hg : (g : GL (Fin p) K) ∈ normalizer (Th : Set (GL (Fin p) K))) : M.c g ∈ stabSub Tb := by
  have fwd : ∀ g : ↥M.𝔾, (g : GL (Fin p) K) ∈ normalizer (Th : Set (GL (Fin p) K)) →
      ∀ t ∈ Tb, M.c g t ∈ Tb := by
    intro g hg t ht
    obtain ⟨A, rfl⟩ := M.ι_surj t
    obtain ⟨s, hs, z, hAz⟩ := hL.dec A ht
    obtain ⟨hsH, -⟩ := hL.mem s hs
    have hgs : (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ ∈ Th :=
      (Subgroup.mem_normalizer_iff.1 hg s).1 hs
    obtain ⟨hgsH, hgsT⟩ := hL.mem _ hgs
    have hzH : (GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) ∈ M.H := by
      have : GeneralLinearGroup.scalar (Fin p) z = s⁻¹ * (A : GL (Fin p) K) := by
        rw [hAz]
        group
      rw [this]
      exact M.H.mul_mem (M.H.inv_mem hsH) A.2
    have e : M.conjH g A = ⟨_, hgsH⟩ * ⟨GeneralLinearGroup.scalar (Fin p) z, hzH⟩ := by
      apply Subtype.ext
      change (g : GL (Fin p) K) * (A : GL (Fin p) K) * (g : GL (Fin p) K)⁻¹ =
        ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹) * GeneralLinearGroup.scalar (Fin p) z
      rw [hAz]
      have h1 : GeneralLinearGroup.scalar (Fin p) z * (g : GL (Fin p) K)⁻¹ =
          (g : GL (Fin p) K)⁻¹ * GeneralLinearGroup.scalar (Fin p) z := scalar_comm z _
      calc (g : GL (Fin p) K) * (s * GeneralLinearGroup.scalar (Fin p) z) * (g : GL (Fin p) K)⁻¹
          = (g : GL (Fin p) K) * s * (GeneralLinearGroup.scalar (Fin p) z *
              (g : GL (Fin p) K)⁻¹) := by group
        _ = _ := by rw [h1]; group
    rw [M.c_ι', e, map_mul]
    have : M.ι ⟨GeneralLinearGroup.scalar (Fin p) z, hzH⟩ = 1 := (M.ι_eq_one _).2 ⟨z, rfl⟩
    rw [this, mul_one]
    exact hgsT
  intro t
  refine ⟨fwd g hg t, fun h => ?_⟩
  have hginv : ((g⁻¹ : ↥M.𝔾) : GL (Fin p) K) ∈ normalizer (Th : Set (GL (Fin p) K)) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hg
  have := fwd g⁻¹ hginv _ h
  rwa [map_inv, MulAut.inv_apply_self] at this

theorem MatModel.IsLift.fix_iff_mem_centralizer (hL : M.IsLift Tb Th) (hp : p.Prime)
    (hp2 : p ≠ 2) {g : ↥M.𝔾} :
    (∀ t ∈ Tb, M.c g t = t) ↔
      (g : GL (Fin p) K) ∈ centralizer (Th : Set (GL (Fin p) K)) := by
  constructor
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨hsH, hsT⟩ := hL.mem s hs
    have h1 : M.ι (M.conjH g ⟨s, hsH⟩) = M.ι ⟨s, hsH⟩ := by
      rw [← M.c_ι' g ⟨s, hsH⟩]
      exact hfix _ hsT
    have h2 : M.ι (M.conjH g ⟨s, hsH⟩ * ⟨s, hsH⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨z, hz⟩ := (M.ι_eq_one _).1 h2
    have hz' : (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ * s⁻¹ =
        GeneralLinearGroup.scalar (Fin p) z := hz
    have hzH : (GeneralLinearGroup.scalar (Fin p) z : GL (Fin p) K) ∈ M.H := by
      rw [← hz']
      exact M.H.mul_mem (M.norm_mem g g.2 s hsH) (M.H.inv_mem hsH)
    have hzp : z ^ p = 1 := MatModel.scalar_pow_eq_one hzH
    have hgs : (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin p) z * s := by
      calc (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹
          = ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ * s⁻¹) * s := by group
        _ = _ := by rw [hz']
    obtain ⟨k, hk⟩ := hL.two ⟨s, hs⟩
    have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hz2 : z ^ (2 ^ k) = 1 := by
      have h3 : ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹) ^ (2 ^ k) = 1 := by
        rw [conj_pow, hk']
        group
      rw [hgs] at h3
      have hcomm : Commute (GeneralLinearGroup.scalar (Fin p) z) s := scalar_comm z s
      rw [hcomm.mul_pow, hk', mul_one, ← map_pow] at h3
      exact scalar_eq_one hp.ne_zero (by rw [h3])
    have hz1 : z = 1 := eq_one_of_two_elt_p_elt hp hp2 ⟨k, hz2⟩ ⟨1, by simpa using hzp⟩
    rw [hz1, map_one, one_mul] at hgs
    calc s * (g : GL (Fin p) K) = ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹) *
          (g : GL (Fin p) K) := by rw [hgs]
      _ = (g : GL (Fin p) K) * s := by group
  · intro hg t ht
    obtain ⟨A, rfl⟩ := M.ι_surj t
    obtain ⟨s, hs, z, hAz⟩ := hL.dec A ht
    obtain ⟨hsH, -⟩ := hL.mem s hs
    have hcs : (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ = s := by
      have := Subgroup.mem_centralizer_iff.1 hg s hs
      calc (g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹ = s * (g : GL (Fin p) K) *
          (g : GL (Fin p) K)⁻¹ := by rw [this]
        _ = s := by group
    rw [M.c_ι']
    congr 1
    apply Subtype.ext
    change (g : GL (Fin p) K) * (A : GL (Fin p) K) * (g : GL (Fin p) K)⁻¹ = (A : GL (Fin p) K)
    rw [hAz]
    have h1 : GeneralLinearGroup.scalar (Fin p) z * (g : GL (Fin p) K)⁻¹ =
        (g : GL (Fin p) K)⁻¹ * GeneralLinearGroup.scalar (Fin p) z := scalar_comm z _
    calc (g : GL (Fin p) K) * (s * GeneralLinearGroup.scalar (Fin p) z) * (g : GL (Fin p) K)⁻¹
        = (g : GL (Fin p) K) * s * (GeneralLinearGroup.scalar (Fin p) z *
            (g : GL (Fin p) K)⁻¹) := by group
      _ = ((g : GL (Fin p) K) * s * (g : GL (Fin p) K)⁻¹) *
          GeneralLinearGroup.scalar (Fin p) z := by
        rw [h1]
        group
      _ = _ := by rw [hcs]

end Interface

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
