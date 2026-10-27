module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinInner
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open scoped MatrixGroups

theorem b_structure_of_inner {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hinn : ∀ b ∈ B, ∃ s : ↥S, InducesInnerModCentre S b s) :
    B = Subgroup.zpowers x ⊔ B ⊓ S ∧ IsElemAbelian p (modCentreImage S B) ∧
      Nat.card B = p * Nat.card (modCentreImage S B) := by
  classical
  have hp : p.Prime := hcfg.prime
  haveI hSN : S.Normal := hcfg.normal
  haveI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup Ω := Subgroup.centralizer (S : Set Ω)
  let N : Subgroup ↥C := (S ⊓ C).subgroupOf C
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, ?_⟩
    · have hgS : (g : Ω) ∈ Subgroup.normalizer (S : Set Ω) :=
        Subgroup.centralizer_le_normalizer (S : Set Ω) g.2
      exact (Subgroup.mem_normalizer_iff.mp hgS (n : Ω)).1 hn.1
    · change (g : Ω) * (n : Ω) * (g : Ω)⁻¹ ∈ C
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hgl : l * (g : Ω) = (g : Ω) * l :=
        Subgroup.mem_centralizer_iff.mp g.2 l hl
      have hnl : l * (n : Ω) = (n : Ω) * l :=
        Subgroup.mem_centralizer_iff.mp hn.2 l hl
      have hgl' : l * (g : Ω)⁻¹ = (g : Ω)⁻¹ * l := by
        have hgl'' : (g : Ω) * l = l * (g : Ω) := hgl.symm
        calc l * (g : Ω)⁻¹
            = (g : Ω)⁻¹ * ((g : Ω) * (l * (g : Ω)⁻¹)) := by group
          _ = (g : Ω)⁻¹ * (((g : Ω) * l) * (g : Ω)⁻¹) := by group
          _ = (g : Ω)⁻¹ * ((l * (g : Ω)) * (g : Ω)⁻¹) := by rw [hgl'']
          _ = (g : Ω)⁻¹ * l := by group
      calc l * ((g : Ω) * (n : Ω) * (g : Ω)⁻¹)
          = (l * (g : Ω)) * (n : Ω) * (g : Ω)⁻¹ := by group
        _ = ((g : Ω) * l) * (n : Ω) * (g : Ω)⁻¹ := by rw [hgl]
        _ = (g : Ω) * (l * (n : Ω)) * (g : Ω)⁻¹ := by group
        _ = (g : Ω) * ((n : Ω) * l) * (g : Ω)⁻¹ := by rw [hnl]
        _ = (g : Ω) * (n : Ω) * (l * (g : Ω)⁻¹) := by group
        _ = (g : Ω) * (n : Ω) * ((g : Ω)⁻¹ * l) := by rw [hgl']
        _ = ((g : Ω) * (n : Ω) * (g : Ω)⁻¹) * l := by group
  choose s hs using fun b : ↥B => hinn b b.2
  have hnormalize : ∀ b : ↥B, MulAut.conjNormal (b : Ω)⁻¹ = MulAut.conj (s b) := by
    intro b
    refine CFSG.GorensteinWalter.perfect_central_automorphism_eq ⟨hcfg.qs.1⟩ _ _ ?_
    intro l
    obtain ⟨z, hz, hz_eq⟩ := hs b l
    have hval : (MulAut.conjNormal (b : Ω)⁻¹) l * ((MulAut.conj (s b)) l)⁻¹ = z := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, MulAut.conj_apply,
        inv_inv]
      rw [hz_eq]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hcomm : (↑(s b) * ↑l * (↑(s b))⁻¹) * (↑z : Ω) =
          (↑z : Ω) * (↑(s b) * ↑l * (↑(s b))⁻¹) := by
        have hy := congrArg (fun x : ↥S => (x : Ω))
          (Subgroup.mem_center_iff.mp hz (s b * l * (s b)⁻¹))
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hy
      rw [hcomm]
      group
    rw [hval]
    exact hz
  have hcC : ∀ b : ↥B, (b : Ω) * (s b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
    intro b
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hconj : (b : Ω)⁻¹ * l * (b : Ω) = (s b : Ω) * l * (s b : Ω)⁻¹ := by
      have h := congrArg (fun f : MulAut ↥S => ((f ⟨l, hl⟩ : ↥S) : Ω)) (hnormalize b)
      simpa only [MulAut.conjNormal_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
        Subgroup.coe_inv, Subtype.coe_mk] using h
    calc l * ((b : Ω) * (s b : Ω))
        = (b : Ω) * ((b : Ω)⁻¹ * l * (b : Ω)) * (s b : Ω) := by group
      _ = (b : Ω) * ((s b : Ω) * l * (s b : Ω)⁻¹) * (s b : Ω) := by rw [hconj]
      _ = ((b : Ω) * (s b : Ω)) * l := by group
  let c : ↥B → ↥C := fun b => ⟨(b : Ω) * (s b : Ω), hcC b⟩
  have hc_coe : ∀ b : ↥B, (c b : Ω) = (b : Ω) * (s b : Ω) := fun _ => rfl
  have hb_coe : ∀ b : ↥B, (b : Ω) = (c b : Ω) * (s b : Ω)⁻¹ := by
    intro b
    rw [hc_coe]
    group
  have hindep : ∀ (b : ↥B) (c' : ↥C) (t : ↥S),
      (b : Ω) = (c' : Ω) * (t : Ω)⁻¹ → c'⁻¹ * c b ∈ N := by
    intro b c' t h
    have h1 : (c' : Ω) * (t : Ω)⁻¹ = (c b : Ω) * (s b : Ω)⁻¹ := by
      rw [← h, hb_coe]
    have hval : ((c'⁻¹ * c b : ↥C) : Ω) = (t : Ω)⁻¹ * (s b : Ω) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (c' : Ω)⁻¹ * (c b : Ω)
          = (c' : Ω)⁻¹ * ((c' : Ω) * (t : Ω)⁻¹) * (s b : Ω) := by
              rw [h1]; group
        _ = (t : Ω)⁻¹ * (s b : Ω) := by group
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact Subgroup.mul_mem S (Subgroup.inv_mem S t.2) (s b).2
    · change (c' : Ω)⁻¹ * (c b : Ω) ∈ C
      exact Subgroup.mul_mem C (Subgroup.inv_mem C c'.2) (c b).2
  let φ : ↥B →* ↥C ⧸ N :=
    { toFun := fun b => QuotientGroup.mk' N (c b)
      map_one' := by
        have h1 := hindep 1 1 1 (by simp)
        have hc1 : c 1 ∈ N := by simpa using h1
        exact (QuotientGroup.eq_one_iff (N := N) (c 1)).2 hc1
      map_mul' := by
        intro b1 b2
        have h1 := hindep (b1 * b2) (c b1 * c b2) (s b2 * s b1) ?_
        · exact ((QuotientGroup.mk'_eq_mk' (N := N) (x := c b1 * c b2)
            (y := c (b1 * b2))).2
            ⟨(c b1 * c b2)⁻¹ * c (b1 * b2), h1, by group⟩).symm
        · have e1 := hb_coe b1
          have e2 := hb_coe b2
          have hc2_comm : (c b2 : Ω) * (s b1 : Ω)⁻¹ = (s b1 : Ω)⁻¹ * (c b2 : Ω) := by
            have hcomm := Subgroup.mem_centralizer_iff.mp (c b2).2 (s b1) (s b1).2
            calc (c b2 : Ω) * (s b1 : Ω)⁻¹
                = ((s b1 : Ω)⁻¹ * (s b1 : Ω)) * (c b2 : Ω) * (s b1 : Ω)⁻¹ := by group
              _ = (s b1 : Ω)⁻¹ * ((s b1 : Ω) * (c b2 : Ω)) * (s b1 : Ω)⁻¹ := by group
              _ = (s b1 : Ω)⁻¹ * ((c b2 : Ω) * (s b1 : Ω)) * (s b1 : Ω)⁻¹ := by rw [hcomm]
              _ = (s b1 : Ω)⁻¹ * (c b2 : Ω) := by group
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [e1, e2]
          calc (c b1 : Ω) * (s b1 : Ω)⁻¹ * ((c b2 : Ω) * (s b2 : Ω)⁻¹)
              = (c b1 : Ω) * (((s b1 : Ω)⁻¹ * (c b2 : Ω)) * (s b2 : Ω)⁻¹) := by group
            _ = (c b1 : Ω) * (((c b2 : Ω) * (s b1 : Ω)⁻¹) * (s b2 : Ω)⁻¹) := by
                rw [← hc2_comm]
            _ = ((c b1 : Ω) * (c b2 : Ω)) * ((s b2 : Ω) * (s b1 : Ω))⁻¹ := by group }
  have hker : φ.ker = (B ⊓ S).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hb1
      have hcN : c b ∈ N := (QuotientGroup.eq_one_iff (N := N) (c b)).1 hb1
      have hcS : (c b : Ω) ∈ S := (Subgroup.mem_subgroupOf.mp hcN).1
      have hbS : (b : Ω) ∈ S := by
        rw [hb_coe b]
        exact Subgroup.mul_mem S hcS (Subgroup.inv_mem S (s b).2)
      exact ⟨b.2, hbS⟩
    · intro hb
      have hbS : (b : Ω) ∈ S := hb.2
      have hcS : (c b : Ω) ∈ S := by
        have hbc : (c b : Ω) = (b : Ω) * (s b : Ω) := hc_coe b
        rw [hbc]
        exact Subgroup.mul_mem S hbS (s b).2
      have hcN : c b ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hcS, (c b).2⟩
      exact (QuotientGroup.eq_one_iff (N := N) (c b)).2 hcN
  have hker_card : Nat.card φ.ker = Nat.card ↥(B ⊓ S) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ S ≤ B)).toEquiv
  have hxC : x ∈ C := (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  let xC : ↥C := ⟨x, hxC⟩
  have hφx_eq : φ ⟨x, hcfg.mem⟩ = QuotientGroup.mk' N xC := by
    have h1 := hindep ⟨x, hcfg.mem⟩ xC 1 (by simp [xC])
    exact ((QuotientGroup.mk'_eq_mk' (N := N) (x := xC)
      (y := c ⟨x, hcfg.mem⟩)).2
      ⟨xC⁻¹ * c ⟨x, hcfg.mem⟩, h1, by group⟩).symm
  have hxS_not : x ∉ S := by
    intro hxS
    have hxZ : (⟨x, hxS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxC (y : Ω) y.2
    have hxpow : (⟨x, hxS⟩ : ↥S) ^ p = 1 := by
      apply Subtype.ext
      simpa using hcfg.elem.2 x hcfg.mem
    have hxne : (⟨x, hxS⟩ : ↥S) ≠ 1 := by
      intro h
      exact hcfg.ne_one (by simpa using congrArg Subtype.val h)
    have horder : orderOf (⟨x, hxS⟩ : ↥S) = p := orderOf_eq_prime hxpow hxne
    have hdvd : p ∣ Nat.card (Subgroup.center ↥S) := by
      rw [← horder]
      exact Subgroup.orderOf_dvd_natCard _ hxZ
    exact hZ hdvd
  have hxN : xC ∉ N := by
    intro h
    exact hxS_not (Subgroup.mem_subgroupOf.mp h).1
  have hφx_ne : φ ⟨x, hcfg.mem⟩ ≠ 1 := by
    rw [hφx_eq]
    intro h
    exact hxN ((QuotientGroup.eq_one_iff (N := N) xC).1 h)
  have hφx_pow : (φ ⟨x, hcfg.mem⟩) ^ p = 1 := by
    have hxpB : (⟨x, hcfg.mem⟩ : ↥B) ^ p = 1 := by
      apply Subtype.ext
      simpa using hcfg.elem.2 x hcfg.mem
    rw [← map_pow, hxpB, map_one]
  have hzx_card : Nat.card (Subgroup.zpowers (φ ⟨x, hcfg.mem⟩)) = p :=
    card_zpowers_eq_of_pow hp hφx_pow hφx_ne
  have htop_ea : IsElemAbelian p (⊤ : Subgroup ↥B) := by
    refine ⟨IsMulCommutative.of_comm (fun a b => ?_), ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact IsElemAbelian.comm hcfg.elem ((a : ↥B)).2 ((b : ↥B)).2
    · intro a _
      apply Subtype.ext
      exact hcfg.elem.2 ((a : ↥B) : Ω) (a : ↥B).2
  have hrange_p : IsPGroup p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact (isPGroup_of_isElemAbelian htop_ea).map φ
  have hrange_ea : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact IsElemAbelian.map htop_ea φ
  obtain ⟨Et, hEtp, hEtmap, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_lift
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hrange_p
  have hEtcyc : IsCyclic (Et.map C.subtype : Subgroup Ω) := by
    refine hcfg.cyc _ (fun g hg => ?_) (hEtp.map C.subtype)
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    exact centMod_of_mem_centralizer a.2
  have hEtyc : IsCyclic Et :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Et C.subtype C.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective Et C.subtype C.subtype_injective).symm.surjective
  have hrange_cyc : IsCyclic φ.range := by
    rw [← hEtmap]
    let f : ↥Et →* ↥(Et.map (QuotientGroup.mk' N)) :=
      ((QuotientGroup.mk' N).comp Et.subtype).codRestrict _
        (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact isCyclic_of_surjective f hf
  have hrange_card_le : Nat.card φ.range ≤ p :=
    card_le_of_isCyclic_of_pow hp hrange_cyc hrange_ea.2
  have hrange_eq : Subgroup.zpowers (φ ⟨x, hcfg.mem⟩) = φ.range :=
    Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨⟨x, hcfg.mem⟩, rfl⟩))
      (by rw [hzx_card]; exact hrange_card_le)
  have hrange_card : Nat.card φ.range = p := by
    rw [← hrange_eq, hzx_card]
  have hcardB : Nat.card B = p * Nat.card ↥(B ⊓ S) := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hker_card, hrange_card, mul_comm] at h
    simpa using h.symm
  let K : Subgroup ↥S := (B ⊓ S).subgroupOf S
  have hK_eq : K = B.subgroupOf S := by
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact hz.1
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact ⟨hz, z.2⟩
  have hKcenter : K ⊓ Subgroup.center ↥S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).1
    have hzC : z ∈ Subgroup.center ↥S := (Subgroup.mem_inf.mp hz).2
    have hzB : (z : Ω) ∈ B := (Subgroup.mem_subgroupOf.mp hzK).1
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hcfg.elem.2 (z : Ω) hzB
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥S)) :=
      hp.coprime_iff_not_dvd.mpr hZ
    have hdvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have hdvd2 : orderOf z ∣ Nat.card (Subgroup.center ↥S) :=
      Subgroup.orderOf_dvd_natCard _ hzC
    have hone : orderOf z = 1 := by
      have hgcd : orderOf z ∣ Nat.gcd p (Nat.card (Subgroup.center ↥S)) :=
        Nat.dvd_gcd hdvd hdvd2
      rw [hcop.gcd_eq_one] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact orderOf_eq_one_iff.mp hone
  have hmod_eq : modCentreImage S B =
      K.map (QuotientGroup.mk' (Subgroup.center ↥S)) := by
    change (B.subgroupOf S).map (QuotientGroup.mk' (Subgroup.center ↥S)) =
      K.map (QuotientGroup.mk' (Subgroup.center ↥S))
    rw [← hK_eq]
  have hmod_card : Nat.card (modCentreImage S B) = Nat.card ↥(B ⊓ S) := by
    rw [hmod_eq]
    have hbij : Function.Bijective (fun k : ↥K =>
        (⟨(QuotientGroup.mk' (Subgroup.center ↥S)) (k : ↥S), by
          exact Subgroup.mem_map.mpr ⟨(k : ↥S), k.2, rfl⟩⟩ :
          ↥(K.map (QuotientGroup.mk' (Subgroup.center ↥S))))) := by
      constructor
      · intro k1 k2 h
        have hq : (QuotientGroup.mk' (Subgroup.center ↥S))
            ((k1 : ↥S) * (k2 : ↥S)⁻¹) = 1 := by
          rw [map_mul, map_inv]
          rw [show (QuotientGroup.mk' (Subgroup.center ↥S)) (k1 : ↥S) =
            (QuotientGroup.mk' (Subgroup.center ↥S)) (k2 : ↥S) from
            congrArg Subtype.val h]
          simp
        have hmemcenter : (k1 : ↥S) * (k2 : ↥S)⁻¹ ∈ Subgroup.center ↥S :=
          (QuotientGroup.eq_one_iff _).1 hq
        have hmemK : (k1 : ↥S) * (k2 : ↥S)⁻¹ ∈ K :=
          Subgroup.mul_mem K k1.2 (Subgroup.inv_mem K k2.2)
        have hbot : (k1 : ↥S) * (k2 : ↥S)⁻¹ = 1 := by
          have hmem : (k1 : ↥S) * (k2 : ↥S)⁻¹ ∈ K ⊓ Subgroup.center ↥S :=
            Subgroup.mem_inf.mpr ⟨hmemK, hmemcenter⟩
          rw [hKcenter] at hmem
          exact Subgroup.mem_bot.mp hmem
        exact Subtype.ext (mul_inv_eq_one.mp hbot)
      · intro y
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
    calc Nat.card (K.map (QuotientGroup.mk' (Subgroup.center ↥S)))
        = Nat.card ↥K := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
      _ = Nat.card ↥(B ⊓ S) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ S ≤ S)).toEquiv
  have hBsup : B = Subgroup.zpowers x ⊔ B ⊓ S := by
    apply le_antisymm
    · intro b hb
      let bb : ↥B := ⟨b, hb⟩
      have hmem : φ bb ∈ Subgroup.zpowers (φ ⟨x, hcfg.mem⟩) := by
        rw [hrange_eq]
        exact MonoidHom.mem_range.mpr ⟨bb, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hxkB : x ^ k ∈ B :=
        (Subgroup.zpowers_le.mpr hcfg.mem) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      have hxk_eq : (⟨x ^ k, hxkB⟩ : ↥B) = ⟨x, hcfg.mem⟩ ^ k := by
        apply Subtype.ext
        simp
      have hmap : φ bb = φ ⟨x ^ k, hxkB⟩ := by
        rw [← hk]
        rw [hxk_eq, map_zpow]
      have hker_mem : bb * (⟨x ^ k, hxkB⟩ : ↥B)⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmap, mul_inv_cancel]
      have hmem_inf : ((bb * (⟨x ^ k, hxkB⟩ : ↥B)⁻¹ : ↥B) : Ω) ∈ B ⊓ S := by
        have h := hker_mem
        rw [hker] at h
        exact Subgroup.mem_subgroupOf.mp h
      have hcomm : (x ^ k) * (bb : Ω) = (bb : Ω) * (x ^ k) :=
        IsElemAbelian.comm hcfg.elem hxkB bb.2
      have hmem_prod : (x ^ k) * ((bb * (⟨x ^ k, hxkB⟩ : ↥B)⁻¹ : ↥B) : Ω) ∈
          Subgroup.zpowers x ⊔ B ⊓ S :=
        Subgroup.mul_mem_sup (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) hmem_inf
      convert hmem_prod using 1
      symm
      calc (x ^ k) * ((bb * (⟨x ^ k, hxkB⟩ : ↥B)⁻¹ : ↥B) : Ω)
          = (x ^ k) * ((bb : Ω) * (x ^ k)⁻¹) := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        _ = (bb : Ω) := by
              calc (x ^ k) * ((bb : Ω) * (x ^ k)⁻¹)
                  = ((x ^ k) * (bb : Ω)) * (x ^ k)⁻¹ := by group
                _ = ((bb : Ω) * (x ^ k)) * (x ^ k)⁻¹ := by rw [hcomm]
                _ = (bb : Ω) := by group
        _ = b := rfl
    · exact sup_le (Subgroup.zpowers_le.mpr hcfg.mem) inf_le_left
  refine ⟨hBsup, ?_, ?_⟩
  · simpa [modCentreImage] using
      (IsElemAbelian.map (IsElemAbelian.subgroupOf hcfg.elem S)
        (QuotientGroup.mk' (Subgroup.center ↥S)))
  · rw [hcardB, ← hmod_card]

theorem lin_B_structure {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {n d : ℕ} {F : Type} [Field F] [Finite F]
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LinPSL d F} (hM : LinMarking p S B n d F θ)
    (hn : 2 ≤ n) (hd : ¬ p ∣ d) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    B = Subgroup.zpowers x ⊔ B ⊓ S ∧ IsElemAbelian p (modCentreImage S B) ∧
      Nat.card B = p * Nat.card (modCentreImage S B) := by
  refine b_structure_of_inner hcfg hZ fun b hb => ?_
  obtain ⟨φ, hφ, hind⟩ := hM.2.2.2.2.2.2 b hb
  have hbp : b ^ p = 1 := hcfg.elem.2 b hb
  have hn1 : p ∣ 2 ^ n - 1 := by
    rcases hM.2.2.2.2.1 with h1 | ⟨h1, -⟩
    · exact h1
    · omega
  have harith : LinArith p n d F := ⟨hcfg.prime, hcfg.odd, hn1, hd, hM.1, hn, hM.2.2.1⟩
  haveI := hcfg.normal
  let α : MulAut ↥S := MulAut.conjNormal b⁻¹
  have hα : ∀ l : ↥S, ((α l : ↥S) : Ω) = b⁻¹ * (l : Ω) * b := by
    intro l
    simp [α, MulAut.conjNormal_apply]
  have hαp : α ^ p = 1 := by
    have h1 : α ^ p = MulAut.conjNormal (b⁻¹ ^ p) := (map_pow MulAut.conjNormal b⁻¹ p).symm
    rw [h1, inv_pow, hbp, inv_one, map_one]
  have hstep : ∀ l : ↥S, φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (α l)) :=
    fun l => hind l (α l) (hα l)
  have hiter : ∀ (k : ℕ) (l : ↥S),
      (φ ^ k) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk ((α ^ k) l)) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hstep l, ih]
  have hφp : φ ^ p = 1 := by
    ext y
    obtain ⟨q, rfl⟩ := θ.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hiter p l, hαp]
    simp
  obtain ⟨r, hr⟩ := lin_conjImage_pPower_inner harith hφ hφp
  obtain ⟨s, hs⟩ : ∃ s : ↥S, θ (QuotientGroup.mk s) = r := by
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, hq⟩
  refine ⟨s, fun l => ?_⟩
  have h1 : θ (QuotientGroup.mk (s * l * s⁻¹)) = θ (QuotientGroup.mk (α l)) := by
    have e1 : θ (QuotientGroup.mk (s * l * s⁻¹)) = r * θ (QuotientGroup.mk l) * r⁻¹ := by
      rw [← hs]
      simp
    rw [e1, ← hr]
    exact hstep l
  have h2 : (QuotientGroup.mk (s * l * s⁻¹) : ↥S ⧸ Subgroup.center ↥S) =
      QuotientGroup.mk (α l) := θ.injective h1
  rw [QuotientGroup.eq] at h2
  refine ⟨(s * l * s⁻¹)⁻¹ * α l, h2, ?_⟩
  rw [mul_inv_cancel_left]
  exact (hα l).symm

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
