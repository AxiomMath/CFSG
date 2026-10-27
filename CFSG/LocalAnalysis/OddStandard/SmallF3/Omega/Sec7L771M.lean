module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l771_inf_cent_bot [Finite G] (hP : Asc82Tab6P) {K : Subgroup G}
    (hK : IsOm6P K) : K ⊓ centralizer (K : Set G) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
  have hz : w ∈ centerIn K := by
    refine Subgroup.mem_map.mpr ⟨⟨w, hw.1⟩, Subgroup.mem_center_iff.mpr fun a => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hw.2 (a : G) a.2)
  rw [hP.center_triv G K hK] at hz
  exact Subgroup.mem_bot.mp hz

theorem sec7l771_main [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (h76 : Asc82Lemma76) (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hE1 : Asc82E8Cent)
    (hE2 : Asc82E8Stab) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    IsElemAb2 (ASub S B ⊓ CFSG.conjugate L g) 4 ∧
      QuotEquivTo (CFSG.conjugate L g ⊓ MSub S B) (CFSG.conjugate L g ⊓ ASub S B)
        (Equiv.Perm (Fin 5)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hctx := hc.ctx
  have hL : IsOm6P L := hctx.isOm6P
  have hc' := hctx.conjugate g
  have hK : IsOm6P (CFSG.conjugate L g) := hc'.isOm6P
  have hsC : g⁻¹ * t * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hc'.t_mem_centralizer
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hc'.involution
  have hcycK : ∀ P : Subgroup G,
      IsSylow2Of P (centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)) → IsCyclic P :=
    h72 G (g⁻¹ * t * g) (CFSG.conjugate L g) hc'.toSec3SettingLB hc'.omega6
  have hCs : ∀ c : G, c * (g⁻¹ * t * g) = (g⁻¹ * t * g) * c →
      c ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := fun c hcs =>
    hc'.cent_le_normalizer h36 c (Subgroup.mem_centralizer_singleton_iff.mpr hcs)
  have hZK : CFSG.conjugate L g ⊓ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) = ⊥ :=
    sec7l771_inf_cent_bot hP hK
  have hout := hP.out_two G (CFSG.conjugate L g) hK
  obtain ⟨φ, hφ⟩ := sec7l78_act_of_aut_B hP hL (hctx.isSylow2Of_inf h36) hc.normalE16
  have hPN : IsSylow2Of (S ⊓ L) (L ⊓ normalizer (B : Set G)) := sec7l771_sylow_N h36 hc
  obtain ⟨hzB, hz1, hzP⟩ := sec7l771_z_facts h36 hP hc
  obtain ⟨E, hEB, hE8, hzE, hPE, hEgen, ν₀, hν₀N, hν₀3, -, hν₀z, hν₀E, hν₀C⟩ :=
    sec7l771_E_exists hφ hPN hzB hz1 hzP
  have hAc := sec7l78_A_comm_sq h36 h76 hP hc
  have hsA : g⁻¹ * t * g ∈ ASub S B := sec7l78_s_mem_A hP h36 hc
  have hBA : B ≤ ASub S B := sec7l77_B_le_A hc
  have hAK : ∀ a ∈ ASub S B, a ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    fun a ha => hCs a (hAc.1 a ha _ hsA)
  have hAB : ∀ a ∈ ASub S B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hAc.1 a ha b (hBA hb)
  have hEK : E ≤ CFSG.conjugate L g :=
    sec7l771_E_le_K hZK hcycK hout hsC hs2 hCs (fun b hb => hAc.1 b (hBA hb) _ hsA)
      (fun b hb => hAc.2 b (hBA hb)) (fun n hn b hb => hφ.conj_mem_B hn hb)
      (fun ν hν hνz => sec7l771_cent_s h36 h76 hP hc hν hνz) hEgen
  have hν₀K : ν₀ ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hCs ν₀ (sec7l771_cent_s h36 h76 hP hc hν₀N hν₀z)
  obtain ⟨l, hlK, hl3, hlE, hlz⟩ := sec7l771_l_of_nu hZK hout hν₀K hν₀3 hE8 hEK hν₀E hν₀C
  have hzK : z ∈ CFSG.conjugate L g := hEK hzE
  have hzI4 : IsI4PlusIn (CFSG.conjugate L g) z :=
    sec7l771_z_type hP hF h73 hctx hzK (hctx.central _ hc.s_mem).symm
  obtain ⟨⟨P', hP'syl, hP'D, -⟩, hcentD, hrel⟩ :=
    hE1 G (CFSG.conjugate L g) hK E z l hE8 hEK hzE hzI4 hlK hl3 hlE hlz
  have hDA : CFSG.conjugate L g ⊓ centralizer (E : Set G) ≤ ASub S B := by
    rcases hc.choice with hcase | hcase
    · have hSs : ∀ x ∈ S, x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := by
        intro x hx
        have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hx)
        have hxz : x * z = z * x := hctx.central x hx
        rw [hcase]
        calc x * (t * z) = (x * t) * z := by group
          _ = (t * x) * z := by rw [hxt]
          _ = t * (x * z) := by group
          _ = t * (z * x) := by rw [hxz]
          _ = (t * z) * x := by group
      have hSN : ∀ x ∈ S, x ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
        fun x hx => hCs x (hSs x hx)
      have hle : S ≤ centralizer ({g⁻¹ * t * g} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hSs x hx)
      have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({g⁻¹ * t * g} : Set G)) :=
        CFSG.ABGLocalTools.isSylowOf_iff.mpr (sec5_isSylow2Of_centralizer_conj hctx.sylow rfl hle)
      have hSyl : IsSylow2Of (S ⊓ CFSG.conjugate L g) (CFSG.conjugate L g) :=
        CFSG.ABGLocalTools.isSylowOf_iff.mp
          (hS'.inf_of_le_normalizer hc'.le_centralizer (hc'.cent_le_normalizer h36))
      have hY : Nat.card ↥(S ⊓ L) = 128 := by
        rw [hφ.card_sylow hPN]
        norm_num
      have hYK : S ⊓ L ≤ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
        fun x hx => hSN x hx.1
      have hYC : S ⊓ L ⊓ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) = ⊥ :=
        sec7l771_inf_C_bot hZK hYK (hctx.isSylow2Of_inf h36).2.1 hzK hz1
          (sec7l771_ZP h36 hP hc)
      have hCL : ∀ B' : Subgroup G, IsNormalE16In (S ⊓ L) B' → ∀ y ∈ S ⊓ L,
          (∀ b ∈ B', y * b = b * y) → y ∈ B' := by
        intro B' hB' y hy hyc
        have hCB' := (hP.aut_B G L hL (S ⊓ L) (hctx.isSylow2Of_inf h36) B' hB').2.1
        rw [← hCB']
        exact ⟨hy.2, Subgroup.mem_centralizer_iff.mpr fun b hb => (hyc b hb).symm⟩
      have hPEn : S ⊓ CFSG.conjugate L g ≤ normalizer (E : Set G) :=
        sec7l771_D_le_S_a hE2 hK hSyl hSN hE8 hEK hctx.mem_S hzE hctx.central hlK hl3 hlE hlz
          hY hYC hPE hCL
      have hD2 : IsPGroup 2 ↥(CFSG.conjugate L g ⊓ centralizer (E : Set G)) :=
        IsPGroup.of_card (n := 4) hP'D.2.1.2
      have hDS := sec7l771_D_le_S_good hSyl hPEn hD2
      refine sec7l771_le_A hDS ?_ ?_
      · intro d hd b hb
        have hbK : b ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
          hAK b (hBA hb)
        exact (hcentD b hbK (fun e he => hAB b (hBA hb) e (hEB he)) d hd).symm
      · intro d hd
        have h := hP'D.2.1.1.2 d hd
        rwa [pow_two] at h
    · have hA64 : 64 ≤ Nat.card (ASub S B) :=
        sec7l771_card_A_b h36 h76 hP hc hcase.1 hcase.2.2.1
      exact sec7l771_D_le_A_b hZK hcycK hAc.1 hAc.2 hsA hsC hs2 hAK
        (fun a ha e he => hAB a ha e (hEB he)) hrel hA64
  have hAut := hP.aut_B G (CFSG.conjugate L g) hK P' hP'syl _ hP'D
  have hKD : ∀ x ∈ CFSG.conjugate L g, (∀ d ∈ CFSG.conjugate L g ⊓ centralizer (E : Set G),
      x * d = d * x) → x ∈ CFSG.conjugate L g ⊓ centralizer (E : Set G) := by
    intro x hx hxc
    have hmem : x ∈ CFSG.conjugate L g ⊓ centralizer
        ((CFSG.conjugate L g ⊓ centralizer (E : Set G) : Subgroup G) : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun d hd => (hxc d hd).symm⟩
    rwa [hAut.2.1] at hmem
  exact sec7l771_conclude hAK
    (fun a ha d hd => hcentD a (hAK a ha) (fun e he => hAB a ha e (hEB he)) d hd) hDA inf_le_left
    (fun a ha haK => ⟨haK, Subgroup.mem_centralizer_iff.mpr fun e he =>
      (hAB a ha e (hEB he)).symm⟩) hKD hP'D.2.1 hAut.1

end CFSG.OddStandard.SmallF3.Omega
