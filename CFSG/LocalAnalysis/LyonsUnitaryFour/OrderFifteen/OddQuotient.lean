module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SylowAutomorphism
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormalizerQuotient

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.RankTwoShapes

section Helpers

variable {G : Type*} [Group G]

instance sup_centralizer_subgroupOf_normalizer_inf_normal (Q C : Subgroup G) :
    ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G) ⊓ C)).Normal where
  conj_mem x hx m := by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := (sup_centralizer_subgroupOf_normalizer_normal Q).conj_mem
      ⟨x, x.2.1⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨m, m.2.1⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h

@[expose] noncomputable def normalizerOuterAction (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) →*
      MulAut (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) ⧸
        (MulAut.conj : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) →*
          MulAut (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))).range :=
  haveI := Subgroup.normal_in_normalizer (H := Q)
  (QuotientGroup.mk' _).comp
    (MulAut.conjNormal (H := Q.subgroupOf (Subgroup.normalizer (Q : Set G))))

theorem ker_normalizerOuterAction (Q : Subgroup G) :
    (normalizerOuterAction Q).ker =
      (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)) := by
  have := Subgroup.normal_in_normalizer (H := Q)
  ext n
  rw [MonoidHom.mem_ker, normalizerOuterAction, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨p, hp⟩
    have hpQ : (((p : Subgroup.normalizer (Q : Set G))) : G) ∈ Q := p.2
    have hc : (((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ * n ∈
        Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : (⟨q, Subgroup.le_normalizer hq⟩ : Subgroup.normalizer (Q : Set G)) ∈
          Q.subgroupOf (Subgroup.normalizer (Q : Set G)) := hq
      have h := congrArg (fun φ : MulAut (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) =>
        (((φ ⟨_, hq'⟩ : Q.subgroupOf (Subgroup.normalizer (Q : Set G))) :
          Subgroup.normalizer (Q : Set G)) : G)) hp
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc q * ((((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ * n)
          = (((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ *
              ((((p : Subgroup.normalizer (Q : Set G))) : G) * q *
                (((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹) * n := by group
        _ = (((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ * ((n : G) * q * (n : G)⁻¹) * n := by
            rw [h]
        _ = (((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ * n * q := by group
    have hn : (n : G) = (((p : Subgroup.normalizer (Q : Set G))) : G) *
        ((((p : Subgroup.normalizer (Q : Set G))) : G)⁻¹ * n) := by group
    rw [hn]
    exact Subgroup.mul_mem_sup hpQ hc
  · intro hn
    have hn' : (n : G) ∈ ((Q ⊔ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := hn
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q _ (le_normalizer_centralizer Q),
      Set.mem_mul] at hn'
    obtain ⟨q, hq, c, hc, hqc⟩ := hn'
    refine ⟨⟨⟨q, Subgroup.le_normalizer hq⟩, hq⟩, MulEquiv.ext fun x => Subtype.ext
      (Subtype.ext ?_)⟩
    have hx : (((x : Subgroup.normalizer (Q : Set G))) : G) ∈ Q := x.2
    have hcx := (Subgroup.mem_centralizer_iff.mp hc) _ hx
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hqc]
    calc q * (((x : Subgroup.normalizer (Q : Set G))) : G) * q⁻¹
        = q * ((((x : Subgroup.normalizer (Q : Set G))) : G) * c) * c⁻¹ * q⁻¹ := by group
      _ = q * (c * (((x : Subgroup.normalizer (Q : Set G))) : G)) * c⁻¹ * q⁻¹ := by rw [hcx]
      _ = q * c * (((x : Subgroup.normalizer (Q : Set G))) : G) * (q * c)⁻¹ := by group

theorem map_normalizer_subgroupOf_eq {S C : Subgroup G} (hSC : S ≤ C) :
    (Subgroup.normalizer ((S.subgroupOf C : Subgroup C) : Set C)).map C.subtype =
      Subgroup.normalizer (S : Set G) ⊓ C := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro g
    constructor
    · intro hg
      have h := (hy ⟨g, hSC hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · intro hg
      have hg' : (y : G) * g * (y : G)⁻¹ ∈ S := hg
      have hgC : g ∈ C := by
        have h := C.mul_mem (C.mul_mem (C.inv_mem y.2) (hSC hg')) y.2
        simpa [mul_assoc] using h
      have h := (hy ⟨g, hgC⟩).mpr (by
        rw [Subgroup.mem_subgroupOf]
        simpa using hg')
      rw [Subgroup.mem_subgroupOf] at h
      exact h
  · rintro ⟨hxN, hxC⟩
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hxN g

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem lyons_unitary_four_normalizer_odd_quotient [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal ∧
    IsCyclic (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      ((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) ∧
    ((((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3 ∨
      (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15) ∧
    ∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      (Subgroup.normalizer (((S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) :
          Subgroup (Subgroup.centralizer ({z} : Set G))) :
            Set (Subgroup.centralizer ({z} : Set G)))).map
          (Subgroup.centralizer ({z} : Set G)).subtype =
        Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ∧
      (S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G) =
        (S : Subgroup G) ⊔ (Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G)) ∧
      (S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
        Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ Subgroup.centralizer
          (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) :
            Set G) ∧
      IsCyclic ((Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G) : Subgroup G) ⧸
        ((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))) ∧
      (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))).index =
        (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G))).index / 3 ∧
      ((((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))).index = 1 ∨
        (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))).index = 5) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, hidx3, -, -, hloc⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set Cs := Subgroup.centralizer (Sg : Set G) with hCs
  set R := Sg ⊔ Cs with hR
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  have hSN : Sg ≤ N := Subgroup.le_normalizer
  have hCsN : Cs ≤ N := Subgroup.centralizer_le_normalizer _
  have hRN : R ≤ N := sup_le hSN hCsN
  have hGF : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨eU⟩ := nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hGF
  let e : Sg.subgroupOf N ≃* unitaryFourW (GaloisField 2 4) hGF :=
    (Subgroup.subgroupOfEquivOfLe hSN).trans (hSU.some.trans eU)
  set θ := normalizerOuterAction Sg with hθ
  have hker : θ.ker = R.subgroupOf N := ker_normalizerOuterAction Sg
  let eq : N ⧸ R.subgroupOf N ≃* θ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange θ)
  have hcardR : Nat.card θ.range = (R.subgroupOf N).index := (Nat.card_congr eq.toEquiv).symm
  have hodd : Odd (R.subgroupOf N).index := by
    have hSyl : ¬ 2 ∣ (Sg.subgroupOf N).index := by
      have := (S.subtype hSN).not_dvd_index
      rwa [Sylow.coe_subtype] at this
    have hle : Sg.subgroupOf N ≤ R.subgroupOf N := fun s hs => by
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      exact le_sup_left (a := Sg) (b := Cs) hs
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSyl))
      (Subgroup.index_dvd_of_le hle)
  obtain ⟨hcyc, hdvd15⟩ := odd_subgroup_outer_unitaryFourW e θ.range (hcardR ▸ hodd)
  have hcycN : IsCyclic (N ⧸ R.subgroupOf N) := isCyclic_of_injective eq.toMonoidHom eq.injective
  rw [hcardR] at hdvd15
  have hRZ : R ≤ Subgroup.centralizer (Z : Set G) := by
    apply sup_le
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact ((mem_map_center_iff.mp hw).2 s hs).symm
    · intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp hm) w (mem_map_center_iff.mp hw).1
  have h3 : 3 ∣ (R.subgroupOf N).index := by
    rw [← hidx3]
    exact Subgroup.index_dvd_of_le fun n hn => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hRZ hn
  have hd : (R.subgroupOf N).index = 3 ∨ (R.subgroupOf N).index = 15 := by
    have hle : (R.subgroupOf N).index ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd15
    interval_cases h : (R.subgroupOf N).index <;> simp_all
  refine ⟨inferInstance, hcycN, hd, fun z hzZ hz1 => ?_⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hSC : Sg ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_map_center_iff.mp hzZ).2 s hs)
  have hCsC : Cs ≤ C := fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hc) z (mem_map_center_iff.mp hzZ).1).symm
  have hRM : R ≤ N ⊓ C := le_inf hRN (sup_le hSC hCsC)
  have hMZ : N ⊓ C = N ⊓ Subgroup.centralizer (Z : Set G) := (hloc z hzZ hz1).1
  set ι := Subgroup.inclusion (inf_le_left : N ⊓ C ≤ N) with hι
  have hcomap : R.subgroupOf (N ⊓ C) ≤ (R.subgroupOf N).comap ι := fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp hx
  set φ := QuotientGroup.map (R.subgroupOf (N ⊓ C)) (R.subgroupOf N) ι hcomap with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ, QuotientGroup.map_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq
  have hcycM : IsCyclic ((N ⊓ C : Subgroup G) ⧸ R.subgroupOf (N ⊓ C)) :=
    isCyclic_of_injective φ hφinj
  have hMN : (N ⊓ C).relIndex N = 3 := by
    rw [hMZ, Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
    exact hidx3
  have hmul := Subgroup.relIndex_mul_relIndex R (N ⊓ C) N hRM inf_le_left
  rw [hMN] at hmul
  have hidxM : (R.subgroupOf (N ⊓ C)).index = (R.subgroupOf N).index / 3 := by
    change R.relIndex (N ⊓ C) = R.relIndex N / 3
    omega
  refine ⟨map_normalizer_subgroupOf_eq hSC, by rw [inf_eq_left.mpr hCsC], hRM, hMZ, hcycM,
    hidxM, ?_⟩
  rw [hidxM]
  omega

end CFSG.LyonsUnitaryFour
