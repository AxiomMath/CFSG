module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBP1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7c_conjSub_K7 (c : Ctx7 G L) (hb : B7Std c) {x : G} (hx : x ∈ y7cX c.s) :
    conjSub x (K7 c.s) = K7 c.s := by
  have key : ∀ y : G, (conjSub y (JF c.s ⊔ M3 c.s)).map (MulAut.conj x).toMonoidHom
      = conjSub (x * y) (JF c.s ⊔ M3 c.s) := by
    intro y
    rw [conjSub, Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : conjSub x (K7 c.s) = (K7 c.s).map (MulAut.conj x).toMonoidHom := rfl
  rw [hmap, K7, Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, key]
  apply le_antisymm
  · refine iSup₂_le fun y hy => le_iSup₂_of_le (x * y) ((y7cX c.s).mul_mem hx hy) le_rfl
  · refine iSup₂_le fun y hy => ?_
    refine le_iSup₂_of_le (x⁻¹ * y) ((y7cX c.s).mul_mem ((y7cX c.s).inv_mem hx) hy) ?_
    exact le_of_eq (by rw [mul_inv_cancel_left])

theorem y7c_K7_eq_pre (c : Ctx7 G L) (hb : B7Std c) :
    K7 c.s = y7cPre c.s (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))) := by
  let N : Subgroup (y7cGam c.s) := Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))
  haveI hNn : N.Normal := Subgroup.normalClosure_normal
  let H : Subgroup G := JF c.s ⊔ M3 c.s
  have hHX : H ≤ y7cX c.s := sup_le (y7c_JF_le_X c hb) (y7c_M3_le_X c.s)
  have hHM : M3 c.s ≤ H := le_sup_right
  have hImgM : y7cImg c.s (M3 c.s) = ⊥ := by
    have h := y7cImg_pre c.s (⊥ : Subgroup (y7cGam c.s))
    rw [y7cPre_bot] at h
    exact h
  have hImgH : y7cImg c.s H = y7cJC c := by
    show y7cImg c.s (JF c.s ⊔ M3 c.s) = y7cJC c
    rw [y7cImg_sup c.s (y7c_JF_le_X c hb) (y7c_M3_le_X c.s), hImgM, sup_bot_eq]
  have hPreJ : y7cPre c.s (y7cJC c) = H := by
    rw [← hImgH]
    exact y7cPre_img c.s hHX hHM
  have hle : K7 c.s ≤ y7cPre c.s N := by
    rw [K7]
    refine iSup₂_le fun x hx => ?_
    have hconj : conjSub x H = y7cPre c.s (conjSub (y7cPi c.s ⟨x, hx⟩) (y7cJC c)) := by
      rw [← hPreJ]
      exact (y7cPre_conj c.s ⟨x, hx⟩ (y7cJC c)).symm
    rw [hconj]
    refine (y7cPre_mono c.s).mpr ?_
    calc conjSub (y7cPi c.s ⟨x, hx⟩) (y7cJC c)
        ≤ conjSub (y7cPi c.s ⟨x, hx⟩) N :=
          Subgroup.map_mono (f := (MulAut.conj (y7cPi c.s ⟨x, hx⟩)).toMonoidHom)
            Subgroup.le_normalClosure
      _ = N := Subgroup.Normal.map_conj_eq N _
  have hKleX : K7 c.s ≤ y7cX c.s := hle.trans (y7cPre_le_X c.s N)
  have hMleK : M3 c.s ≤ K7 c.s := by
    rw [K7]
    refine le_trans ?_ (le_iSup₂_of_le (1 : G) (Subgroup.one_mem (y7cX c.s)) le_rfl)
    intro m hm
    rw [conjSub, Subgroup.mem_map]
    exact ⟨m, Subgroup.mem_sup_right hm, by simp [MulAut.conj_apply]⟩
  have hJleKbar : y7cJC c ≤ y7cImg c.s (K7 c.s) :=
    y7cImg_mono c.s (y7c_JF_le_K7 c.s)
  have hKbar_normal : (y7cImg c.s (K7 c.s)).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    obtain ⟨x, rfl⟩ := y7cPi_surjective c.s g
    calc (y7cImg c.s (K7 c.s)).map (MulAut.conj (y7cPi c.s x)).toMonoidHom
        = conjSub (y7cPi c.s x) (y7cImg c.s (K7 c.s)) := rfl
      _ = y7cImg c.s (conjSub (x : G) (K7 c.s)) := (y7cImg_conj c.s x (K7 c.s)).symm
      _ = y7cImg c.s (K7 c.s) := by rw [y7c_conjSub_K7 c hb x.2]
  have hNleKbar : N ≤ y7cImg c.s (K7 c.s) :=
    Subgroup.normalClosure_le_normal hJleKbar
  have hPreNleK : y7cPre c.s N ≤ K7 c.s := by
    have h := (y7cPre_mono c.s).mpr hNleKbar
    rwa [y7cPre_img c.s hKleX hMleK] at h
  exact le_antisymm hle hPreNleK

theorem y7c_K7_le_X (c : Ctx7 G L) (hb : B7Std c) : K7 c.s ≤ y7cX c.s := by
  rw [y7c_K7_eq_pre c hb]
  exact y7cPre_le_X c.s _

theorem y7c_M3_le_K7 (c : Ctx7 G L) (hb : B7Std c) : M3 c.s ≤ K7 c.s := by
  rw [y7c_K7_eq_pre c hb]
  exact y7c_M3_le_pre c.s _

theorem y7c_K7_norm (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x ∈ y7cX c.s, ∀ k ∈ K7 c.s, x * k * x⁻¹ ∈ K7 c.s := by
  intro x hx k hk
  rw [y7c_K7_eq_pre c hb] at hk ⊢
  obtain ⟨hkX, hkπ⟩ := (mem_y7cPre c.s).mp hk
  have hmem : x * k * x⁻¹ ∈ y7cX c.s :=
    (y7cX c.s).mul_mem ((y7cX c.s).mul_mem hx hkX) ((y7cX c.s).inv_mem hx)
  refine (mem_y7cPre c.s).mpr ⟨hmem, ?_⟩
  have h1 : y7cPi c.s ⟨x * k * x⁻¹, hmem⟩
      = y7cPi c.s ⟨x, hx⟩ * y7cPi c.s ⟨k, hkX⟩ * (y7cPi c.s ⟨x, hx⟩)⁻¹ := by
    have hsub : (⟨x * k * x⁻¹, hmem⟩ : ↥(y7cX c.s))
        = ⟨x, hx⟩ * ⟨k, hkX⟩ * ⟨x, hx⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [hsub]
    simp only [map_mul, map_inv]
  rw [h1]
  haveI hNn : (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))).Normal :=
    Subgroup.normalClosure_normal
  exact hNn.conj_mem _ hkπ _

theorem y7c_secProp_pre {A : Type} [Group A] (s : Setting3 G L) (Y : Subgroup (y7cGam s))
    (hY : Nonempty (↥Y ≃* A)) :
    SecProp (y7cPre s Y) (M3 s) (fun Z _ _ _ => Nonempty (Z ≃* A)) := by
  have hN : ((M3 s).subgroupOf (y7cPre s Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (y7c_M3_le_pre s Y)]
    intro h k hh hk
    have hc := (y7c_M3_normal s).conj_mem ⟨h, y7c_M3_le_X s hh⟩
      (Subgroup.mem_subgroupOf.mpr hh) ⟨k, y7cPre_le_X s Y hk⟩
    rw [Subgroup.mem_subgroupOf] at hc
    simpa using hc
  refine ⟨hN, ?_⟩
  let φ : ↥(y7cPre s Y) →* ↥Y :=
    MonoidHom.codRestrict ((y7cPi s).comp (Subgroup.inclusion (y7cPre_le_X s Y))) Y
      fun x => ((mem_y7cPre s).mp x.2).2
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := y7cPi_surjective s (y : y7cGam s)
    have hxY : (x : G) ∈ y7cPre s Y :=
      (mem_y7cPre s).mpr ⟨x.2, by rw [hx]; exact y.2⟩
    refine ⟨⟨(x : G), hxY⟩, ?_⟩
    apply Subtype.ext
    have hval : ((φ ⟨(x : G), hxY⟩ : ↥Y) : y7cGam s)
        = y7cPi s ⟨(x : G), y7cPre_le_X s Y hxY⟩ := by
      simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
      congr 1
    rw [hval]
    rw [show (⟨(x : G), y7cPre_le_X s Y hxY⟩ : ↥(y7cX s)) = x from Subtype.ext rfl]
    exact hx
  have hker : φ.ker = (M3 s).subgroupOf (y7cPre s Y) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff, Subgroup.coe_one]
    have hval : ((φ x : ↥Y) : y7cGam s) = y7cPi s ⟨(x : G), y7cPre_le_X s Y x.2⟩ := by
      simp only [φ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
      congr 1
    rw [hval, y7cPi_eq_one_iff]
  obtain ⟨e⟩ := hY
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).trans e)⟩

theorem y7c_isCompPre_pre (c : Ctx7 G L) (hb : B7Std c) {Y : Subgroup (y7cGam c.s)}
    (hY : Nonempty (↥Y ≃* GL3Two))
    (hd : IsInternalDirect (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))) Y
      (conjSub (y7cTC c hb) Y)) :
    IsCompPre c.s (y7cPre c.s Y) := by
  have hL1t : conjSub c.s.t (y7cPre c.s Y) = y7cPre c.s (conjSub (y7cTC c hb) Y) :=
    (y7cPre_conj c.s ⟨c.s.t, y7c_t_mem_X c hb⟩ Y).symm
  refine ⟨y7c_M3_le_pre c.s Y, ?_, ?_, ?_, ?_, y7c_secProp_pre c.s Y hY⟩
  · rw [y7c_K7_eq_pre c hb]
    exact (y7cPre_mono c.s).mpr (le_sup_left.trans (le_of_eq hd.1))
  · rw [y7c_K7_eq_pre c hb, hL1t, ← y7cPre_sup, hd.1]
  · rw [hL1t, ← y7cPre_inf, hd.2.1, y7cPre_bot]
  · rw [hL1t, Subgroup.commutator_le]
    intro a ha b hb'
    have haX : a ∈ y7cX c.s := y7cPre_le_X c.s Y ha
    have hbX : b ∈ y7cX c.s := y7cPre_le_X c.s (conjSub (y7cTC c hb) Y) hb'
    have hpa : y7cPi c.s ⟨a, haX⟩ ∈ Y := ((mem_y7cPre c.s).mp ha).2
    have hpb : y7cPi c.s ⟨b, hbX⟩ ∈ conjSub (y7cTC c hb) Y :=
      ((mem_y7cPre c.s).mp hb').2
    have hcomm : y7cPi c.s ⟨a, haX⟩ * y7cPi c.s ⟨b, hbX⟩
        = y7cPi c.s ⟨b, hbX⟩ * y7cPi c.s ⟨a, haX⟩ := hd.2.2 _ hpa _ hpb
    have hmemb : ⁅a, b⁆ ∈ y7cX c.s := by
      rw [commutatorElement_def]
      exact (y7cX c.s).mul_mem ((y7cX c.s).mul_mem ((y7cX c.s).mul_mem haX hbX)
        ((y7cX c.s).inv_mem haX)) ((y7cX c.s).inv_mem hbX)
    apply (y7cPi_eq_one_iff c.s ⟨⁅a, b⁆, hmemb⟩).mp
    have hsub : (⟨⁅a, b⁆, hmemb⟩ : ↥(y7cX c.s)) = ⁅(⟨a, haX⟩ : ↥(y7cX c.s)), ⟨b, hbX⟩⁆ := by
      ext
      simp [commutatorElement_def]
    rw [hsub, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm

theorem y7c_sylow_pre (c : Ctx7 G L) (hb : B7Std c)
    (hS : IsSylowIn 2 (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))) (y7cPC c)) :
    IsSylowIn 2 (K7 c.s) (P7 c.e) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPreP : y7cPre c.s (y7cImg c.s (P7 c.e)) = P7 c.e :=
    y7cPre_img c.s (y7c_P7_le_X c hb) (y7c_M3_le_P7 c hb)
  have hPK : P7 c.e ≤ K7 c.s := by
    rw [← hPreP, y7c_K7_eq_pre c hb]
    exact (y7cPre_mono c.s).mpr hS.1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(y7cPC c))).mp hS.2.1
  have hcardP : Nat.card ↥(P7 c.e) = 2 ^ (a + 6) := by
    rw [← hPreP, y7c_card_pre c.s (y7cImg c.s (P7 c.e)), ha,
      y7c_card_M3 c.toCtx5 hb.hH, ← pow_add]
  refine ⟨hPK, IsPGroup.of_card hcardP, ?_⟩
  have hrelK := Subgroup.relIndex_mul_card (H := P7 c.e) (K := K7 c.s)
  rw [inf_of_le_left hPK] at hrelK
  have hrelN := Subgroup.relIndex_mul_card (H := y7cPC c)
    (K := Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
  rw [inf_of_le_left hS.1] at hrelN
  have hcardPreK : Nat.card ↥(K7 c.s)
      = Nat.card ↥(Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
        * Nat.card ↥(M3 c.s) := by
    rw [y7c_K7_eq_pre c hb]
    exact y7c_card_pre c.s _
  have hcardPreP : Nat.card ↥(P7 c.e) = Nat.card ↥(y7cPC c) * Nat.card ↥(M3 c.s) := by
    rw [← hPreP]
    exact y7c_card_pre c.s (y7cImg c.s (P7 c.e))
  have h1 : (P7 c.e).relIndex (K7 c.s) * (Nat.card ↥(y7cPC c) * Nat.card ↥(M3 c.s))
      = (y7cPC c).relIndex (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
        * (Nat.card ↥(y7cPC c) * Nat.card ↥(M3 c.s)) := by
    calc (P7 c.e).relIndex (K7 c.s) * (Nat.card ↥(y7cPC c) * Nat.card ↥(M3 c.s))
        = (P7 c.e).relIndex (K7 c.s) * Nat.card ↥(P7 c.e) := by rw [hcardPreP]
      _ = Nat.card ↥(K7 c.s) := hrelK
      _ = Nat.card ↥(Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
            * Nat.card ↥(M3 c.s) := hcardPreK
      _ = ((y7cPC c).relIndex (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
            * Nat.card ↥(y7cPC c)) * Nat.card ↥(M3 c.s) := by rw [hrelN]
      _ = (y7cPC c).relIndex (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
            * (Nat.card ↥(y7cPC c) * Nat.card ↥(M3 c.s)) := by rw [Nat.mul_assoc]
  have h2 : (P7 c.e).relIndex (K7 c.s)
      = (y7cPC c).relIndex (Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s))) :=
    Nat.mul_right_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos) h1
  rw [h2]
  exact hS.2.2

end CFSG.OddStandard.HigherRank.YamadaG23
