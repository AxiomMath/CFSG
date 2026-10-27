module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDecomp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω} {G₀ : Type} [Group G₀]

theorem isPerfect_K (hcfg : Cfg173 p S B N D K x) : Group.IsPerfect ↥K :=
  ⟨hcfg.std.2.2.2.2.2.1.2.2.1⟩

theorem isPerfect_closureIn {K H : Subgroup Ω} (hK : Group.IsPerfect ↥K) : Group.IsPerfect ↥(closureIn K H) := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm (Subgroup.commutator_le_self _)
  unfold closureIn
  refine iSup₂_le fun a ha => ?_
  have hperf : Group.IsPerfect ↥(K.map (MulAut.conj a).toMonoidHom) := by
    haveI : Group.IsPerfect ↥K := hK
    exact Group.IsPerfect.map (MulAut.conj a).toMonoidHom
  rw [← Subgroup.isPerfect_iff.mp hperf]
  exact Subgroup.commutator_mono (le_biSup (fun b => K.map (MulAut.conj b).toMonoidHom) ha)
    (le_biSup (fun b => K.map (MulAut.conj b).toMonoidHom) ha)

private noncomputable def nonempty_pSimple_equiv_conj_aux1 {G G' : Type} [Group G] [Group G']
    {J : Subgroup G} {J' : Subgroup G'} (e : ↥J ≃* ↥J') (p : ℕ) : PSimple p J ≃* PSimple p J' := by
  have hPC : (GLAPPrimeCore p ↥J).map (e : ↥J →* ↥J') = GLAPPrimeCore p ↥J' :=
    CFSG.pPrimeCore_map_iso p e
  let φ : PQuot p J ≃* PQuot p J' :=
    QuotientGroup.congr (GLAPPrimeCore p ↥J) (GLAPPrimeCore p ↥J') e hPC
  exact QuotientGroup.congr (Subgroup.center (PQuot p J)) (Subgroup.center (PQuot p J')) φ
    (Subgroup.map_center_eq φ)

theorem nonempty_pSimple_equiv_conj (p : ℕ) (K : Subgroup Ω) (ν : Ω) :
    Nonempty (PSimple p (K.map (MulAut.conj ν).toMonoidHom) ≃* PSimple p K) :=
  ⟨(nonempty_pSimple_equiv_conj_aux1
    (Subgroup.equivMapOfInjective K (MulAut.conj ν).toMonoidHom (MulAut.conj ν).injective) p).symm⟩

theorem nonempty_pSimple_equiv_piImg (M : S172X.S172Model S B G₀) (hp : p.Prime) {K' : Subgroup Ω} (hK'S : K' ≤ S)
    (hK' : Group.IsPerfect ↥K') : Nonempty (PSimple p K' ≃* PSimple p (piImg M K')) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperfS : Group.IsPerfect ↥(K'.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hK'S).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK'S).symm.surjective
  obtain ⟨eπ⟩ := M.nonempty_pSimple_equiv_map p (K := K'.subgroupOf S) hperfS
  obtain ⟨esub⟩ := nonempty_pQuot_equiv_subgroupOf p hK'S
  refine ⟨?_⟩
  change PSimple p K' ≃* PSimple p ((K'.subgroupOf S).map M.π)
  exact (QuotientGroup.congr _ _ esub (Subgroup.map_center_eq esub)).symm.trans eπ

private theorem exists_std_elt_aux1 {Ω : Type} [Group Ω] {S B D' : Subgroup Ω} {x : Ω}
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x)
    (hD'B : D' ≤ B) (hxD' : x ∈ D') :
    D' ⊓ Subgroup.centralizer (S : Set Ω) = Subgroup.zpowers x := by
  apply le_antisymm
  · intro b hb
    exact (hcent b (hD'B hb.1)).1 hb.2
  · rw [le_inf_iff]
    exact ⟨Subgroup.zpowers_le.2 hxD',
      Subgroup.zpowers_le.2 ((hcent x (hD'B hxD')).2 (Subgroup.mem_zpowers x))⟩

private theorem exists_std_elt_aux2 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {x : Ω}
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x)
    (hmem : x ∈ B) (hne : x ≠ 1) (helem : IsElemAbelian p B) (hp : p.Prime)
    {D' : Subgroup Ω} (hD'B : D' ≤ B) (hxD' : x ∈ D') (hcard : Nat.card D' = p ^ 2) :
    Nat.card (M.img D') = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := M.card_img_mul_card_inf hD'B
  rw [exists_std_elt_aux1 hcent hD'B hxD', Nat.card_zpowers,
    orderOf_eq_prime (helem.2 x hmem) hne, hcard] at h1
  refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
  rw [h1]
  ring

private theorem exists_std_elt_aux3 {Ω : Type} [Group Ω] {S B : Subgroup Ω} {G₀ : Type} [Group G₀]
    (M : S172X.S172Model S B G₀) {D' K' : Subgroup Ω} {d : G₀}
    (hDB : D' ≤ B) (hKeq : K' = GLALayer (S ⊓ Subgroup.centralizer (D' : Set Ω)))
    (hd : M.img D' = Subgroup.zpowers d) :
    piImg M K' = stdLayer d := by
  have hsub : (GLALayer (S ⊓ Subgroup.centralizer (D' : Set Ω))).subgroupOf S =
      GLALayer (S172X.csIn S D') := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((Y10F.glaLayer_le _).trans inf_le_left),
      S172X.glaLayer_csIn_map]
  unfold piImg stdLayer
  rw [hKeq, hsub, ← M.glaLayer_centralizer_img hDB]
  congr 1
  rw [← S172X.centralizer_zpowers_eq d, hd]

theorem exists_std_elt (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀) {D' K' : Subgroup Ω}
    (h' : GLAStdSubPre p B x S D' K') :
    ∃ d : G₀, IsStdElt p M.β.range d ∧ M.img D' = Subgroup.zpowers d ∧ piImg M K' = stdLayer d := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hDB, hDe, hDc, hxmem, hKeq, hKc, hDK⟩ := h'
  have hcard : Nat.card (M.img D') = p :=
    exists_std_elt_aux2 M hcfg.cent hcfg.mem hcfg.ne_one hcfg.elem hp hDB hxmem hDc
  obtain ⟨d, hd⟩ := S172X.exists_zpowers_eq_of_card_eq_prime (p := p) hcard
  have hdr : d ∈ M.β.range := M.img_le_range D' (hd ▸ Subgroup.mem_zpowers d)
  have hcenteq : Subgroup.centralizer (M.img D' : Set G₀) = Subgroup.centralizer ({d} : Set G₀) := by
    rw [← hd, S172X.centralizer_zpowers_eq]
  have hord : orderOf d = p := by
    rw [← Nat.card_zpowers, hd, hcard]
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.ne_one hord.symm
  have hdp : d ^ p = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one d
  have hKc' : IsComponentOf (GLALayer (S ⊓ Subgroup.centralizer (D' : Set Ω)))
      (S ⊓ Subgroup.centralizer (D' : Set Ω)) := by
    rw [← hKeq]; exact hKc
  have hKc'' : IsComponentOf (GLALayer (S172X.csIn S D')) (S172X.csIn S D') :=
    (S172X.isComponentOf_glaLayer_csIn_iff S D').2 hKc'
  have hcomp : IsComponentOf (stdLayer d) (Subgroup.centralizer ({d} : Set G₀)) := by
    change IsComponentOf (GLALayer (Subgroup.centralizer ({d} : Set G₀)))
      (Subgroup.centralizer ({d} : Set G₀))
    rw [← hcenteq]
    exact (M.isComponentOf_glaLayer_centralizer_img_iff hDB).2 hKc''
  refine ⟨d, ⟨hdr, hd1, hdp, hcomp, ?_⟩, hd.symm, exists_std_elt_aux3 M hDB hKeq hd.symm⟩
  rw [stdLayer]
  rw [← hcenteq, ← M.img_cs_glaLayer hDB hKc', ← hKeq, ← M.img_inf_left, ← hDK, ← hd]

private theorem glaStdSubPre_conj_aux1 {Ω : Type} [Group Ω] (φ : MulAut Ω) (D : Subgroup Ω) :
    (Subgroup.centralizer (D : Set Ω)).map φ.toMonoidHom =
      Subgroup.centralizer (D.map φ.toMonoidHom : Set Ω) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro w hw
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hw
    rw [← map_mul, ← map_mul, hz d hd]
  · intro y hy
    refine Subgroup.mem_map.2 ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro d hd
    have h := hy (φ d) (Subgroup.mem_map_of_mem φ.toMonoidHom hd)
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact h

private theorem glaStdSubPre_conj_aux2 {p : ℕ} {Ω : Type} [Group Ω] {D : Subgroup Ω}
    (φ : MulAut Ω) (hD : IsElemAbelian p D) : IsElemAbelian p (D.map φ.toMonoidHom) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
      isElemAbelian_commute hD hx hy]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hD.2 x hx, map_one]

theorem glaStdSubPre_conj (hcfg : Cfg173 p S B N D K x) {ν : Ω} (hν : ν ∈ N) :
    GLAStdSubPre p B x S (D.map (MulAut.conj ν).toMonoidHom) (K.map (MulAut.conj ν).toMonoidHom) := by
  obtain ⟨hDB, hDe, hDc, hxmem, hKeq, hKc, hDK⟩ := hcfg.std
  have hνN : ν ∈ Subgroup.normalizer (B : Set Ω) ⊓ Subgroup.centralizer ({x} : Set Ω) := hcfg.hN ▸ hν
  have hνB : ν ∈ Subgroup.normalizer (B : Set Ω) := hνN.1
  have hνx : ν ∈ Subgroup.centralizer ({x} : Set Ω) := hνN.2
  have hBmap : B.map (MulAut.conj ν).toMonoidHom = B :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hνB
  have hSmap : S.map (MulAut.conj ν).toMonoidHom = S :=
    (Subgroup.normal_iff_map_conj_eq.1 hcfg.normal) ν
  have hxfix : (MulAut.conj ν) x = x := by
    rw [MulAut.conj_apply, ← Subgroup.mem_centralizer_iff.1 hνx x (Set.mem_singleton x)]
    group
  refine ⟨?_, glaStdSubPre_conj_aux2 (MulAut.conj ν) hDe, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hBmap]; exact Subgroup.map_mono hDB
  · rw [Subgroup.card_map_of_injective (MulAut.conj ν).injective, hDc]
  · exact Subgroup.mem_map.2 ⟨x, hxmem, hxfix⟩
  · rw [hKeq, ← Y10F.glaLayer_map (ι := (MulAut.conj ν).toMonoidHom) (MulAut.conj ν).injective]
    congr 1
    rw [Subgroup.map_inf S (Subgroup.centralizer (D : Set Ω)) (MulAut.conj ν).toMonoidHom
      (MulAut.conj ν).injective, hSmap, glaStdSubPre_conj_aux1 (MulAut.conj ν) D]
  · have h := (Y10F.isComponentOf_map_iff (ι := (MulAut.conj ν).toMonoidHom)
      (MulAut.conj ν).injective (L := K) (H := S ⊓ Subgroup.centralizer (D : Set Ω))).2 hKc
    rw [Subgroup.map_inf S (Subgroup.centralizer (D : Set Ω)) (MulAut.conj ν).toMonoidHom
      (MulAut.conj ν).injective, hSmap, glaStdSubPre_conj_aux1 (MulAut.conj ν) D] at h
    exact h
  · rw [hDK, Subgroup.map_inf B (Subgroup.centralizer (K : Set Ω)) (MulAut.conj ν).toMonoidHom
      (MulAut.conj ν).injective, hBmap, glaStdSubPre_conj_aux1 (MulAut.conj ν) K]

private lemma piImg_mono (M : S172X.S172Model S B G₀) {X Y : Subgroup Ω} (h : X ≤ Y) :
    piImg M X ≤ piImg M Y := by
  unfold piImg
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono S h)

private lemma piImg_map_conj_le (M : S172X.S172Model S B G₀) (hS : S.Normal) {X : Subgroup Ω}
    (s : ↥S) :
    (piImg M X).map (MulAut.conj (M.π s)).toMonoidHom ≤
      piImg M (X.map (MulAut.conj (s : Ω)).toMonoidHom) := by
  rintro z ⟨w, hw, hwz⟩
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.1 hw
  rw [← hwz, ← hxw]
  show MulAut.conj (M.π s) (M.π x) ∈ piImg M (X.map (MulAut.conj (s : Ω)).toMonoidHom)
  refine Subgroup.mem_map.2 ⟨s * x * s⁻¹, ?_, ?_⟩
  · show ((s * x * s⁻¹ : ↥S) : Ω) ∈ X.map (MulAut.conj (s : Ω)).toMonoidHom
    have h1 : ((s * x * s⁻¹ : ↥S) : Ω) = MulAut.conj (s : Ω) (x : Ω) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply]
    rw [h1]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.1 hx)
  · show M.π (s * x * s⁻¹) = MulAut.conj (M.π s) (M.π x)
    simp only [map_mul, map_inv, MulAut.conj_apply]

theorem innerClosure_le_piImg (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {d : G₀} (hd : piImg M K = stdLayer d) :
    innerClosure M.β.range d ≤ piImg M (closureIn K N) := by
  unfold innerClosure
  change (⨆ (g : G₀) (_ : g ∈ Subgroup.normalizer (M.β.range : Set G₀)),
      (stdLayer d).map (MulAut.conj g).toMonoidHom) ≤ piImg M (closureIn K N)
  refine iSup₂_le fun g hg => ?_
  have hg' : g ∈ piImg M (Subgroup.normalizer (B : Set Ω)) := by
    rw [piImg_normalizer_eq hcfg M hZ]
    exact hg
  obtain ⟨sS, hsSB, hsSg⟩ := Subgroup.mem_map.1 hg'
  have hsN : (sS : Ω) ∈ N := by
    rw [hcfg.hN]
    refine ⟨Subgroup.mem_subgroupOf.1 hsSB, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact (Subgroup.mem_centralizer_iff.1
      ((hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)) (sS : Ω) sS.2).symm
  rw [← hd, ← hsSg]
  calc (piImg M K).map (MulAut.conj (M.π sS)).toMonoidHom
      ≤ piImg M (K.map (MulAut.conj (sS : Ω)).toMonoidHom) := piImg_map_conj_le M hcfg.normal sS
    _ ≤ piImg M (closureIn K N) :=
        piImg_mono M (le_biSup (fun a => K.map (MulAut.conj a).toMonoidHom) hsN)

private lemma piImg_iSup_le (M : S172X.S172Model S B G₀) {ι : Sort*} (f : ι → Subgroup Ω)
    (hf : ∀ i, f i ≤ S) : piImg M (⨆ i, f i) ≤ ⨆ i, piImg M (f i) := by
  have hEq : (⨆ i, f i).subgroupOf S = ⨆ i, (f i).subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hf), Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hf i)).symm
  unfold piImg
  rw [hEq, Subgroup.map_iSup]

theorem piImg_closureIn_le_stdFamily (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀) {d : G₀}
    (hd : piImg M K = stdLayer d) : piImg M (closureIn K N) ≤ stdFamily p M.β.range d := by
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hKνS : ∀ ν : Ω, K.map (MulAut.conj ν).toMonoidHom ≤ S := by
    intro ν x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    change ν * k * ν⁻¹ ∈ S
    exact hcfg.normal.conj_mem k (hKS hk) ν
  have h1 : piImg M (closureIn K N) ≤
      ⨆ ν : Ω, piImg M (⨆ (_ : ν ∈ N), K.map (MulAut.conj ν).toMonoidHom) := by
    unfold closureIn
    exact piImg_iSup_le M (fun ν => ⨆ (_ : ν ∈ N), K.map (MulAut.conj ν).toMonoidHom)
      (fun ν => iSup_le fun _ => hKνS ν)
  refine h1.trans (iSup_le fun ν => ?_)
  refine (piImg_iSup_le M (fun _ : ν ∈ N => K.map (MulAut.conj ν).toMonoidHom)
    (fun _ => hKνS ν)).trans (iSup_le fun hν => ?_)
  obtain ⟨dν, hstdν, -, hdν⟩ := exists_std_elt hcfg M (glaStdSubPre_conj hcfg hν)
  have hperfKν : Group.IsPerfect ↥(K.map (MulAut.conj ν).toMonoidHom) := by
    haveI : Group.IsPerfect ↥K := isPerfect_K hcfg
    exact Group.IsPerfect.map (MulAut.conj ν).toMonoidHom
  have htype : Nonempty (PSimple p (stdLayer dν) ≃* PSimple p (stdLayer d)) := by
    rw [← hdν, ← hd]
    obtain ⟨e1⟩ := nonempty_pSimple_equiv_piImg M hcfg.prime (hKνS ν) hperfKν
    obtain ⟨e2⟩ := nonempty_pSimple_equiv_conj p K ν
    obtain ⟨e3⟩ := nonempty_pSimple_equiv_piImg M hcfg.prime hKS (isPerfect_K hcfg)
    exact ⟨e1.symm.trans (e2.trans e3)⟩
  rw [hdν]
  exact le_iSup₂_of_le dν ⟨hstdν, htype⟩ le_rfl

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
