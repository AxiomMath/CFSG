module

public import CFSG.GH74.Uniqueness.SU.SU7R
public import CFSG.GH74.Uniqueness.SU.SU7Sec
public import CFSG.GH74.Uniqueness.SU.SU7Op
public import CFSG.GH74.Uniqueness.SU.SU7Gen4
public import CFSG.GH74.Uniqueness.SU.SU7B

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG

namespace L192

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem cent_ne_top (hc : Ctx19 S U M V x z A B R) : centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hz1 := Base.z_ne_one hc.conf
  have hcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({z} : Set G) := by rw [htop]; exact Subgroup.mem_top g
    exact (mem_centralizer_iff.1 this z (Set.mem_singleton z)).symm
  have hs := hc.hyp.simple
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hcen; exact hz1 (Subgroup.mem_bot.1 hcen)
  · obtain ⟨a, b, hab⟩ := hc.hyp.nonab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem exists_surj_alt5_G (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∃ ψ : ↥(centralizer ({z} : Set G)) →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
      ψ.ker = R.subgroupOf (centralizer ({z} : Set G)) ⊔
        pPrimeCore 2 ↥(centralizer ({z} : Set G)) ∧
      ∀ c : ↥(centralizer ({z} : Set G)),
        (∀ r ∈ R.subgroupOf (centralizer ({z} : Set G)),
          c * r * c⁻¹ * r⁻¹ ∈ pPrimeCore 2 ↥(centralizer ({z} : Set G))) →
        c ∈ R.subgroupOf (centralizer ({z} : Set G)) ⊔ pPrimeCore 2 ↥(centralizer ({z} : Set G)) := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hzC : z ∈ C := mem_centralizer_iff.2 (fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh])
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hz2 := Base.z_mul_self hc.conf
  have hz1 := Base.z_ne_one hc.conf
  obtain ⟨hR32, hzR, hsq⟩ := RF.R_facts hc
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  let z₀ : ↥C := ⟨z, hzC⟩
  have hGH : SU0.GHGroup ↥C := SU0.GHGroup.of_kgh hc.hyp.kgh (cent_ne_top hc)
  have hzc : ∀ g : ↥C, g * z₀ = z₀ * g := fun g => Subtype.ext (RF.cent_comm g.2)
  have hzz : z₀ * z₀ = 1 := Subtype.ext hz2
  have hz1' : z₀ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hS₀p : IsPGroup 2 ↥((S : Subgroup G).subgroupOf C) :=
    Bar.isPGroup_subgroupOf S.isPGroup' C
  have hS₀idx : ¬ 2 ∣ ((S : Subgroup G).subgroupOf C).index := fun hd =>
    S.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le hSC))
  have hRS : R.subgroupOf C ≤ (S : Subgroup G).subgroupOf C := fun r hr => hc.c19.R_le hr
  have hzR' : z₀ ∈ R.subgroupOf C := hzR
  have hS128 : Nat.card ((S : Subgroup G).subgroupOf C) = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]; exact hJ.card_S
  have hR32' : Nat.card (R.subgroupOf C) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv]; exact hR32
  have hRnS : ∀ s ∈ (S : Subgroup G).subgroupOf C, ∀ r ∈ R.subgroupOf C,
      s * r * s⁻¹ ∈ R.subgroupOf C := fun s hs r hr =>
    (mem_normalizer_iff.1 (hc.c19.R_normal hs) (r : G)).1 hr
  have hsq' : ∀ r ∈ R.subgroupOf C, r * r = 1 ∨ r * r = z₀ := by
    intro r hr
    rcases hsq (r : G) hr with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hsq2 : ∀ s ∈ (S : Subgroup G).subgroupOf C, s * s ∈ R.subgroupOf C := fun s hs =>
    RF.sq_mem_R hc hs
  have hfaith' : ∀ s ∈ (S : Subgroup G).subgroupOf C,
      (∀ r ∈ R.subgroupOf C, s * r * s⁻¹ * r⁻¹ = 1 ∨ s * r * s⁻¹ * r⁻¹ = z₀) →
        s ∈ R.subgroupOf C := by
    intro s hs hcomm
    refine RF.faithful hc hs (fun r hr => ?_)
    rcases hcomm ⟨r, hRC hr⟩ hr with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hsc' : ∀ r ∈ R.subgroupOf C, ∀ h : ↥C, h⁻¹ * r * h ∈ (S : Subgroup G).subgroupOf C →
      h⁻¹ * r * h ∈ R.subgroupOf C := fun r hr h hy =>
    RF.sc hKI3 hc (r := (r : G)) (h := (h : G)) hr (RF.cent_comm h.2) hy
  have hmemI : ∀ r : ↥C, r ∈ {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀} ↔
      (r : G) ∈ {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
    intro r
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, congrArg Subtype.val h2, fun h => h3 (Subtype.ext h),
        fun h => h4 (Subtype.ext h)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, Subtype.ext h2, fun h => h3 (congrArg Subtype.val h),
        fun h => h4 (congrArg Subtype.val h)⟩
  have hI10' : {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀}.ncard = 10 := by
    have hset : {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀} =
        (Subtype.val : ↥C → G) ⁻¹' {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} :=
      Set.ext hmemI
    rw [hset, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective ?_]
    · exact RF.card_I hc
    · intro g hg
      exact ⟨⟨g, hRC hg.1⟩, rfl⟩
  have hIgen' : Subgroup.closure {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀} =
      R.subgroupOf C := by
    have himage : C.subtype '' {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀} =
        {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
      ext g
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact (hmemI r).1 hr
      · intro hg
        exact ⟨⟨g, hRC hg.1⟩, (hmemI ⟨g, hRC hg.1⟩).2 hg, rfl⟩
    have hcl : (Subgroup.closure {r : ↥C | r ∈ R.subgroupOf C ∧ r * r = 1 ∧ r ≠ 1 ∧ r ≠ z₀}).map
        C.subtype = (R.subgroupOf C).map C.subtype := by
      rw [MonoidHom.map_closure, himage, RF.I_gen hc, Subgroup.map_subgroupOf_eq_of_le hRC]
    exact Subgroup.map_injective C.subtype_injective hcl
  have hIconj' : ∀ r r' : ↥C, r ∈ R.subgroupOf C → r * r = 1 → r ≠ 1 → r ≠ z₀ →
      r' ∈ R.subgroupOf C → r' * r' = 1 → r' ≠ 1 → r' ≠ z₀ → ∃ h : ↥C, h⁻¹ * r * h = r' := by
    obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := RF.exists_u₀ hc
    intro r r' hr hr2 hr1 hrz hr' hr'2 hr'1 hr'z
    obtain ⟨g₁, hg₁z, hg₁⟩ := RF.I_conj hc hu₀U hu₀1 hu₀z (r := (r : G))
      (Subgroup.mem_subgroupOf.1 hr) (congrArg Subtype.val hr2)
      (fun h => hr1 (Subtype.ext h)) (fun h => hrz (Subtype.ext h))
    obtain ⟨g₂, hg₂z, hg₂⟩ := RF.I_conj hc hu₀U hu₀1 hu₀z (r := (r' : G))
      (Subgroup.mem_subgroupOf.1 hr') (congrArg Subtype.val hr'2)
      (fun h => hr'1 (Subtype.ext h)) (fun h => hr'z (Subtype.ext h))
    have hg₁C : g₁ ∈ C := mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hg₁z.symm)
    have hg₂C : g₂ ∈ C := mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hg₂z.symm)
    refine ⟨⟨g₁, hg₁C⟩ * ⟨g₂, hg₂C⟩⁻¹, Subtype.ext ?_⟩
    show (g₁ * g₂⁻¹)⁻¹ * (r : G) * (g₁ * g₂⁻¹) = r'
    calc (g₁ * g₂⁻¹)⁻¹ * (r : G) * (g₁ * g₂⁻¹) = g₂ * (g₁⁻¹ * r * g₁) * g₂⁻¹ := by group
      _ = g₂ * u₀ * g₂⁻¹ := by rw [hg₁]
      _ = r' := by rw [← hg₂]; group
  exact Sec.exists_surj_alt5 hKI4 hGH hzc hzz hz1' hS₀p hS₀idx hRS hzR' hS128 hR32' hRnS hsq'
    hsq2 hfaith' hsc' hI10' hIgen' hIconj'

theorem op_eq (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    Op_p'p 2 ↥(centralizer ({z} : Set G)) =
      R.subgroupOf (centralizer ({z} : Set G)) ⊔ pPrimeCore 2 ↥(centralizer ({z} : Set G)) := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  obtain ⟨ψ, hψ, hker, -⟩ := exists_surj_alt5_G hKI3 hKI4 hc
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hRp : IsPGroup 2 ↥R := S.isPGroup'.to_le hc.c19.R_le
  have hR₀p : IsPGroup 2 ↥(R.subgroupOf C) := Bar.isPGroup_subgroupOf hRp C
  have hO : pPrimeCore 2 ↥C ≤ ψ.ker := by rw [hker]; exact le_sup_right
  have hbar : ψ.ker.map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) =
      (R.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) := by
    rw [hker, Subgroup.map_sup]
    have : (pPrimeCore 2 ↥C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, sup_bot_eq]
  have h2 : IsPGroup 2 ↥(ψ.ker.map (QuotientGroup.mk' (pPrimeCore 2 ↥C))) := by
    rw [hbar]
    exact hR₀p.map _
  rw [Gen.op_eq_ker ψ hψ hO h2, hker]

theorem lemma192_a (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    IsSylowIn ((Op_p'p 2 ↥(centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype) R ∧
      Nonempty (↥(centralizer ({z} : Set G)) ⧸ Op_p'p 2 ↥(centralizer ({z} : Set G)) ≃*
        alternatingGroup (Fin 5)) := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  obtain ⟨ψ, hψ, hker, -⟩ := exists_surj_alt5_G hKI3 hKI4 hc
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hRp : IsPGroup 2 ↥R := S.isPGroup'.to_le hc.c19.R_le
  have hR₀p : IsPGroup 2 ↥(R.subgroupOf C) := Bar.isPGroup_subgroupOf hRp C
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hOp : Op_p'p 2 ↥C = ψ.ker := (op_eq hKI3 hKI4 hc).trans hker.symm
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hOp).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩
  rw [hOp, hker]
  unfold IsSylowIn
  refine ⟨?_, hRp, ?_⟩
  · intro r hr
    exact ⟨⟨r, hRC hr⟩, Subgroup.mem_sup_left hr, rfl⟩
  · have hrel := Subgroup.relIndex_map_map_of_injective (f := C.subtype) (R.subgroupOf C)
      (R.subgroupOf C ⊔ pPrimeCore 2 ↥C) C.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hRC] at hrel
    rw [hrel, Gen.relIndex_sup_odd (pPrimeCore 2 ↥C) hR₀p hOodd]
    exact hOodd

theorem lemma192_b (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ¬ normalizer (R : Set G) ≤ M := by
  classical
  intro hN
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  obtain ⟨ψ, hψ, hker, -⟩ := exists_surj_alt5_G hKI3 hKI4 hc
  have hSC : (S : Subgroup G) ≤ C := fun s hs =>
    mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hc.conf.z_center s hs).symm)
  have hRC : R ≤ C := hc.c19.R_le.trans hSC
  have hRp : IsPGroup 2 ↥R := S.isPGroup'.to_le hc.c19.R_le
  have hR₀p : IsPGroup 2 ↥(R.subgroupOf C) := Bar.isPGroup_subgroupOf hRp C
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
    Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hxS := Base.x_mem_S hc.conf
  have hxT : x ∉ Tsub S U := hJ.x_not_mem
  have hx2 := hc.conf.hx
  obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := RF.exists_u₀ hc
  obtain ⟨g, hgC, hg⟩ := lemma191 G S U M V x z A B R hc x hxS hxT hx2 u₀ hu₀U hu₀1 hu₀z
  have hKn : ∀ h : ↥C, ∀ r ∈ R.subgroupOf C,
      h * r * h⁻¹ ∈ R.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
    intro h r hr
    rw [← hker]
    have hrk : r ∈ ψ.ker := by rw [hker]; exact Subgroup.mem_sup_left hr
    rw [MonoidHom.mem_ker] at hrk ⊢
    rw [map_mul, map_mul, map_inv, hrk]
    group
  obtain ⟨n, hnN, r₁, hr₁, hnr⟩ := Gen.exists_normalizer_conj (R := R.subgroupOf C)
    (O := pPrimeCore 2 ↥C) hR₀p hOodd hKn ⟨g, hgC⟩
  have hnR : (n : G) ∈ normalizer (R : Set G) := by
    apply Gen.mem_normalizer_of_conj_le
    intro y hy
    exact (mem_normalizer_iff.1 hnN ⟨y, hRC hy⟩).1 hy
  have hnM : (n : G) ∈ M := hN hnR
  have hu₀2 : u₀ * u₀ = 1 := by
    rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 u₀ hu₀U
  have hu₀ord : orderOf u₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu₀2) hu₀1
  have hu₀R : u₀ ∈ R := (hc.c19.R_invol u₀ hu₀ord).2 (Or.inl hu₀U)
  have hxR : x ∈ R := (hc.c19.R_invol x hx2).2 (Or.inr ⟨hxS, hxT⟩)
  have hgu : g * u₀ * g⁻¹ = x := by rw [← hg]; group
  have hnr' := hnr ⟨u₀, hRC hu₀R⟩ hu₀R (by
    show g * u₀ * g⁻¹ ∈ R
    rw [hgu]; exact hxR)
  have hnr'' : (n : G) * u₀ * (n : G)⁻¹ = (r₁ : G) * x * (r₁ : G)⁻¹ := by
    have := congrArg Subtype.val hnr'
    simpa [hgu] using this
  have hr₁R : (r₁ : G) ∈ R := hr₁
  have hy : (n : G) * u₀ * (n : G)⁻¹ ∈ (S : Subgroup G) := by
    rw [hnr'']
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem (hc.c19.R_le hr₁R) hxS)
      ((S : Subgroup G).inv_mem (hc.c19.R_le hr₁R))
  have hT := Claim.conj_mem_T hKI3 hc.hyp hc.conf hc.concl hnM hu₀U hy
  rw [hnr''] at hT
  apply hxT
  have := hJ.T_normal ((r₁ : G)⁻¹) ((S : Subgroup G).inv_mem (hc.c19.R_le hr₁R)) _ hT
  simpa [mul_assoc] using this

end L192

end CFSG.GH74.Uniqueness.SU.SU7
