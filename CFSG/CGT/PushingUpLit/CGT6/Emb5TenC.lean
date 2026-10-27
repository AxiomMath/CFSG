module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenA
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NineB

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open Equiv.Perm (viaEmbeddingHom)
open scoped commutatorElement

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]; simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]; simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]; simp [Nat.card_eq_fintype_card, Nat.factorial]

set_option maxRecDepth 100000 in
theorem five_noncomm :
    (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 3 4) * (Equiv.swap 0 1 * Equiv.swap 1 2) ≠
      (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 3 * Equiv.swap 3 4) := by
  decide +kernel

section Block

variable {V : Type} [CommGroup V] {B : Subgroup (MulAut V)} {m : ℕ}

@[expose] noncomputable def AltBlock.mulEquiv (D : AltBlock B m)
    (hR : ∀ b : ↥B, D.θ b = 1 → b = 1) : ↥B ≃* alternatingGroup (Fin (2 * m + 1)) :=
  MulEquiv.ofBijective (D.θ.codRestrict (alternatingGroup (Fin (2 * m + 1))) D.θ_alt)
    ⟨(injective_iff_map_eq_one _).mpr fun b hb => hR b (congrArg Subtype.val hb), fun a => by
      obtain ⟨b, hb⟩ := D.θ_surj a.1 a.2
      exact ⟨b, Subtype.ext hb⟩⟩

end Block

section Sub

variable {V : Type} [CommGroup V]

theorem false_of_subnormal_alt {B Y : Subgroup (MulAut V)} (e : ↥B ≃* alternatingGroup (Fin 5))
    (hYB : Y ≤ B) (h3 : Nat.card ↥Y = 3) (hsub : (Y.subgroupOf B).IsSubnormal) : False := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hmap := Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective hsub
  have hcard : Nat.card ↥((Y.subgroupOf B).map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective]
    rw [← h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
  rcases hmap.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hcard
    omega
  · rw [htop, Subgroup.card_top, card_alt_five] at hcard
    omega

end Sub

section Rho

variable {V : Type} [CommGroup V] {Y L : Subgroup (MulAut V)} {N : ℕ}

@[expose] def TenAlt.rho (A : TenAlt L Y N) : ↥L →* Equiv.Perm (Fin N) :=
  A.eps.comp (lpi L)

end Rho

section Adjacent

variable {V : Type} [CommGroup V] [Finite V] {G T Y L : Subgroup (MulAut V)} {t : MulAut V}

theorem TenCfg.adjacent_block (hc : TenCfg G T Y t L) {N : ℕ} (hN6 : 6 ≤ N) (hN7 : N ≤ 7)
    (A : TenAlt L Y N) (ι₅ : Fin 5 ↪ Fin N) {y0 x : ↥L} (hy0Y : (y0 : MulAut V) ∈ Y)
    (hy0c : A.rho y0 = viaEmbeddingHom ι₅ (Equiv.swap 0 1 * Equiv.swap 1 2))
    (hxd : A.rho (x * y0 * x⁻¹) = viaEmbeddingHom ι₅ (Equiv.swap 0 3 * Equiv.swap 3 4)) :
    ∃ B : Subgroup (MulAut V), Y ≤ B ∧ B ≤ L ∧ (∀ b ∈ B, t * b * t⁻¹ ∈ B) ∧
      (∀ b : ↥L, (b : MulAut V) ∈ B → lpi L b = 1 → b = 1) ∧
      (∀ a ∈ alternatingGroup (Fin 5), ∃ b : ↥L, (b : MulAut V) ∈ B ∧
        A.rho b = viaEmbeddingHom ι₅ a) ∧
      (∀ b : ↥L, (b : MulAut V) ∈ B →
        A.rho b ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι₅)) ∧
      Nonempty (↥B ≃* alternatingGroup (Fin 5)) := by
  classical
  set g : MulAut V := (x : MulAut V) with hg
  have hgG : g ∈ G := hc.layer.le x.2
  have hYG : Y ≤ G := fun y hy => (hc.cfg.adm.hYC hy).1
  set H : Subgroup (MulAut V) := CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t with hH
  have hHG : H ≤ G :=
    sup_le (sup_le (conjSub_le_of_mem hgG hYG) hYG) (Subgroup.zpowers_le.mpr hc.ht.1)
  have hHne : H ≠ G := hc.hforall g hgG
  have hEinj : Function.Injective (viaEmbeddingHom ι₅) := Equiv.Perm.viaEmbeddingHom_injective ι₅
  have hnc : ¬ ∀ a ∈ CGT6E.conjSub g Y, ∀ b ∈ Y, a * b = b * a := by
    intro hcomm
    have h1 := hcomm (g * y0 * g⁻¹) (CGT6E.conj_mem_conjSub hy0Y) y0 hy0Y
    have h2 : (x * y0 * x⁻¹) * y0 = y0 * (x * y0 * x⁻¹) := Subtype.ext h1
    have h3 : A.rho ((x * y0 * x⁻¹) * y0) = A.rho (y0 * (x * y0 * x⁻¹)) := congrArg A.rho h2
    rw [map_mul A.rho (x * y0 * x⁻¹) y0, map_mul A.rho y0 (x * y0 * x⁻¹), hxd, hy0c,
      ← map_mul, ← map_mul] at h3
    exact five_noncomm (hEinj h3)
  obtain ⟨B, m, D, hlift, hperf, hXB, hm2, hm3, hR, hnorm⟩ :=
    hc.cfg.five_nine_struct hc.hV hc.ht hc.ht1 hc.ht2 hgG hHne hnc
  have hYB : Y ≤ B := hlift.1
  have hBH : B ≤ H := hlift.2.1
  have hBG : B ≤ G := hBH.trans hHG
  have hBL : B ≤ L := by
    have hcc : conjClosure Y B = B := Lift5.conjClosure_eq hc.cfg.not_isPGroup_Y hlift
    rw [← hcc]
    exact (conjClosure_mono hBG).trans (hc.layer.conjClosure_eq hc.hYL).le
  have hBinj : ∀ b : ↥L, (b : MulAut V) ∈ B → lpi L b = 1 → b = 1 := by
    intro b hb hb1
    have hbc : b ∈ Subgroup.center ↥L := lpi_eq_one_iff.mp hb1
    have hz : ∀ a : ↥B, a * (⟨b, hb⟩ : ↥B) = ⟨b, hb⟩ * a := fun a =>
      Subtype.ext (congrArg (fun z : ↥L => (z : MulAut V))
        (Subgroup.mem_center_iff.mp hbc ⟨a, hBL a.2⟩))
    have h1 := eq_one_of_central_alt (by omega : 4 ≤ 2 * m + 1) (D.mulEquiv hR) hz
    exact Subtype.ext (congrArg (fun z : ↥B => (z : MulAut V)) h1)
  set TB : Subgroup (LQ L) := tilde (L := L) B with hTB
  have hcardTB : Nat.card ↥TB = Nat.card ↥B := by
    have hinj : Function.Injective ((lpi L).comp (B.subgroupOf L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hz1 : lpi L (z : ↥L) = 1 := hz
      exact Subtype.ext (hBinj z (Subgroup.mem_subgroupOf.mp z.2) hz1)
    have hrange : ((lpi L).comp (B.subgroupOf L).subtype).range = TB := by
      ext z
      constructor
      · rintro ⟨z', rfl⟩
        exact ⟨(z' : ↥L), z'.2, rfl⟩
      · rintro ⟨z', hz', rfl⟩
        exact ⟨⟨z', hz'⟩, rfl⟩
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  set A5 : Subgroup (Equiv.Perm (Fin N)) :=
    (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι₅) with hA5
  have hA5gen : Subgroup.closure {(viaEmbeddingHom ι₅ (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2)),
      (viaEmbeddingHom ι₅ (Equiv.swap 0 3 * Equiv.swap 3 4))} = A5 := by
    have h1 := MonoidHom.map_closure (viaEmbeddingHom ι₅) {(Equiv.swap (0 : Fin 5) 1 *
      Equiv.swap 1 2), (Equiv.swap 0 3 * Equiv.swap 3 4)}
    rw [Set.image_pair] at h1
    rw [← h1, closure_std_five]
  have hA5le : A5 ≤ TB.map A.eps := by
    rw [← hA5gen, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨lpi L y0, mem_tilde.mpr ⟨y0, y0.2, hYB hy0Y, rfl⟩, hy0c⟩
    · exact ⟨lpi L (x * y0 * x⁻¹), mem_tilde.mpr ⟨_, (x * y0 * x⁻¹).2,
        hXB (CGT6E.conj_mem_conjSub hy0Y), rfl⟩, hxd⟩
  have hA5card : Nat.card ↥A5 = 60 := by
    rw [hA5, Subgroup.card_map_of_injective hEinj, card_alt_five]
  rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
  swap
  ·
    exfalso
    have hcardB : Nat.card ↥B = 2520 :=
      (Nat.card_congr (D.mulEquiv hR).toEquiv).trans card_alt_seven
    have hTB2 : Nat.card ↥TB = 2520 := hcardTB.trans hcardB
    have hS : Nat.card (LQ L) = Nat.card (alternatingGroup (Fin N)) := Nat.card_congr A.e.toEquiv
    have hle : Nat.card ↥TB ≤ Nat.card (LQ L) := Subgroup.card_le_card_group TB
    rcases (by omega : N = 6 ∨ N = 7) with rfl | rfl
    · rw [hS, card_alt_six] at hle
      omega
    · have hTBtop : TB = ⊤ :=
        Subgroup.eq_top_of_card_eq TB (by rw [hTB2, hS, card_alt_seven])
      have hLB : L ≤ B := le_of_tilde_eq_top hc.layer.quasi.1 hTBtop
      have hNK : conjClosure Y G ≤ H :=
        (hc.layer.conjClosure_eq hc.hYL).le.trans (hLB.trans hBH)
      exact hHne (hc.cfg.eq_of_conjClosure_le hc.hV hc.ht hc.ht1 hc.ht2 hNK hHG
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  ·
    have hcardB : Nat.card ↥B = 60 :=
      (Nat.card_congr (D.mulEquiv hR).toEquiv).trans card_alt_five
    have hTB2 : Nat.card ↥TB = 60 := hcardTB.trans hcardB
    have hmapcard : Nat.card ↥(TB.map A.eps) = 60 :=
      (Subgroup.card_map_of_injective A.eps_injective).trans hTB2
    have hEq : A5 = TB.map A.eps :=
      Subgroup.eq_of_le_of_card_ge hA5le (by rw [hmapcard, hA5card])
    refine ⟨B, hYB, hBL, ?_, hBinj, ?_, ?_, ⟨D.mulEquiv hR⟩⟩
    · intro b hb
      exact (Subgroup.mem_normalizer_iff.mp
        (hnorm t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))) b).mp hb
    · intro a ha
      have h1 : viaEmbeddingHom ι₅ a ∈ TB.map A.eps := hEq ▸ ⟨a, ha, rfl⟩
      obtain ⟨s, hs, hse⟩ := h1
      obtain ⟨b, hb, rfl⟩ := hs
      exact ⟨b, Subgroup.mem_subgroupOf.mp hb, hse⟩
    · intro b hb
      rw [hEq]
      exact ⟨lpi L b, ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, rfl⟩

theorem TenAlt.block_stable (hc : TenCfg G T Y t L) {N : ℕ} (A : TenAlt L Y N)
    (ι₅ : Fin 5 ↪ Fin N) {B : Subgroup (MulAut V)} (hBn : ∀ b ∈ B, t * b * t⁻¹ ∈ B)
    (hB1 : ∀ a ∈ alternatingGroup (Fin 5), ∃ b : ↥L, (b : MulAut V) ∈ B ∧
      A.rho b = viaEmbeddingHom ι₅ a)
    (hB2 : ∀ b : ↥L, (b : MulAut V) ∈ B →
      A.rho b ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι₅)) :
    ∀ s : LQ L, A.eps s ∈ (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι₅) →
      A.eps (conjQ hc.layer.normal hc.ht.1 s) ∈
        (alternatingGroup (Fin 5)).map (viaEmbeddingHom ι₅) := by
  intro s hs
  obtain ⟨a, ha, hae⟩ := hs
  obtain ⟨b, hbB, hbe⟩ := hB1 a ha
  have hsb : s = lpi L b := A.eps_injective (by rw [← hae]; exact hbe.symm)
  subst hsb
  rw [conjQ_lpi]
  have hmem : ((conjL hc.layer.normal hc.ht.1 b : ↥L) : MulAut V) ∈ B := by
    rw [conjL_apply]
    exact hBn _ hbB
  exact hB2 _ hmem

theorem TenCfg.false_of_six_seven (hc : TenCfg G T Y t L) {N : ℕ} (hN6 : 6 ≤ N) (hN7 : N ≤ 7)
    (A : TenAlt L Y N) : False := by
  classical
  obtain ⟨ι, hcι⟩ : ∃ ι : Fin 6 ↪ Fin N,
      (A.c : Equiv.Perm (Fin N)) = viaEmbeddingHom ι (Equiv.swap 0 1 * Equiv.swap 1 2) :=
    exists_embedding_threeCycle (k := 3) (by omega) A.c3
  obtain ⟨ιP, ιQ, hag, hP4, hcP, hcQ, hdP, hdQ⟩ := two_embeddings ι
  obtain ⟨hρP, hρQ, hsP, hsQ, -, -⟩ := caseC_perm_facts
  set E := viaEmbeddingHom ι with hE
  have hρP_alt : E (Equiv.swap 1 3 * Equiv.swap 2 4) ∈ alternatingGroup (Fin N) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_viaEmbeddingHom]; exact hsP
  have hρQ_alt : E (Equiv.swap 1 3 * Equiv.swap 2 5) ∈ alternatingGroup (Fin N) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_viaEmbeddingHom]; exact hsQ
  obtain ⟨xP, hxP⟩ := A.exists_lift hρP_alt
  obtain ⟨xQ, hxQ⟩ := A.exists_lift hρQ_alt
  obtain ⟨y0, hy0Y, hy0c⟩ := A.exists_y
  have hy0E : A.rho y0 = E (Equiv.swap 0 1 * Equiv.swap 1 2) := hy0c.trans hcι
  have hy0P : A.rho y0 = viaEmbeddingHom ιP (Equiv.swap 0 1 * Equiv.swap 1 2) :=
    hy0E.trans hcP.symm
  have hy0Q : A.rho y0 = viaEmbeddingHom ιQ (Equiv.swap 0 1 * Equiv.swap 1 2) :=
    hy0E.trans hcQ.symm
  have hxdP : A.rho (xP * y0 * xP⁻¹) = viaEmbeddingHom ιP (Equiv.swap 0 3 * Equiv.swap 3 4) := by
    rw [map_mul A.rho (xP * y0) xP⁻¹, map_mul A.rho xP y0, map_inv A.rho xP]
    have e1 : A.rho xP = E (Equiv.swap 1 3 * Equiv.swap 2 4) := hxP
    rw [e1, hy0E, ← map_inv, ← map_mul, ← map_mul, hρP, hdP]
  have hxdQ : A.rho (xQ * y0 * xQ⁻¹) = viaEmbeddingHom ιQ (Equiv.swap 0 3 * Equiv.swap 3 4) := by
    rw [map_mul A.rho (xQ * y0) xQ⁻¹, map_mul A.rho xQ y0, map_inv A.rho xQ]
    have e1 : A.rho xQ = E (Equiv.swap 1 3 * Equiv.swap 2 5) := hxQ
    rw [e1, hy0E, ← map_inv, ← map_mul, ← map_mul, hρQ, hdQ]
  obtain ⟨BP, hYBP, hBPL, hBPn, hBPinj, hBP1, hBP2, ⟨eBP⟩⟩ :=
    hc.adjacent_block hN6 hN7 A ιP hy0Y hy0P hxdP
  obtain ⟨BQ, -, -, hBQn, -, hBQ1, hBQ2, -⟩ := hc.adjacent_block hN6 hN7 A ιQ hy0Y hy0Q hxdQ
  have hn := hc.layer.normal
  have htG := hc.ht.1
  have htt : t * t = 1 := by rw [← pow_two]; exact hc.ht2
  have hαy : conjQ hn htG (lpi L y0) = lpi L y0 := by
    rw [conjQ_lpi]
    congr 1
    apply Subtype.ext
    rw [conjL_apply]
    have h1 : (y0 : MulAut V) * t = t * y0 := Subgroup.mem_centralizer_iff.mp hc.ht.2 y0 hy0Y
    rw [← h1]
    group
  have hcore := core_alpha A.eps A.eps_injective (conjQ hn htG) (conjQ_conjQ hn htG htt) ιP ιQ
    hag hP4 (lpi L y0) hy0P hαy
    (fun a ha => by obtain ⟨b, -, hb⟩ := hBP1 a ha; exact ⟨lpi L b, hb⟩)
    (fun a ha => by obtain ⟨b, -, hb⟩ := hBQ1 a ha; exact ⟨lpi L b, hb⟩)
    (A.block_stable hc ιP hBPn hBP1 hBP2) (A.block_stable hc ιQ hBQn hBQ1 hBQ2)
  have hcent : ∀ b ∈ BP, t * b * t⁻¹ = b := by
    intro b hb
    have hbL : b ∈ L := hBPL hb
    set bL : ↥L := ⟨b, hbL⟩ with hbLdef
    have h1 := hcore (lpi L bL) (hBP2 bL hb)
    rw [conjQ_lpi] at h1
    set u : ↥L := conjL hn htG bL with hu
    have hu1 : (u : MulAut V) = t * b * t⁻¹ := conjL_apply hn htG bL
    have huB : (u : MulAut V) ∈ BP := by rw [hu1]; exact hBPn b hb
    have h2 : lpi L (u⁻¹ * bL) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : u⁻¹ * bL = 1 :=
      hBPinj _ (BP.mul_mem (BP.inv_mem huB) hb) h2
    have h4 : u = bL := by
      have := congrArg (fun z : ↥L => u * z) h3
      simpa using this.symm
    rw [← hu1, h4]
  have hBPle : BP ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun b hb =>
    ⟨hc.layer.le (hBPL hb), Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact mul_inv_eq_iff_eq_mul.mp (hcent b hb)⟩
  have hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hBPle
    (hc.cfg.cent t hc.ht hc.ht1 hc.ht2)
  exact false_of_subnormal_alt eBP hYBP hc.cfg.adm.h3 hsub

end Adjacent

end CFSG.CGT.PushingUpLit.CGT6
