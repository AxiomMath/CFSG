module

public import CFSG.Certificates.Kernel.SporSch.McLSylowCountSound
public import CFSG.Certificates.Kernel.SporSch.CountPairProof
public import CFSG.Certificates.Kernel.SporSch.BtKProof
public import CFSG.Certificates.Kernel.SporSch.CntZKProof
public import CFSG.Certificates.Kernel.SporSch.SylowCover

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SylowCount Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem pair11_proved (hsz : szOK n w = true)
    (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH) (hnd : base.toList.Nodup)
    (hk64 : nb ≤ 64)
    (hpA : permOK n w (mask w) (n * w) (PS 0) (PSI 0) = true)
    (hpB : permOK n w (mask w) (n * w) (PS 1) (PSI 1) = true)
    (hAc : canonK n w (mask w) (n * w) (PS 0) = true)
    (hAo : ordIs n w (mask w) (pidn n w) (PS 0) 1 = true)
    (hN : ¬11 ^ 2 ∣ ordK LR nb) {bs : List Nat} (hbs : bs = base.toList)
    {groups : List (List Nat)} (hg : groups.flatten = List.range nb)
    {Z Zi Gc Gi C : Nat} (hpZ : permOK n w (mask w) (n * w) Z Zi = true)
    (hpG : permOK n w (mask w) (n * w) Gc Gi = true)
    (hZc : canonK n w (mask w) (n * w) Z = true) (hGc : canonK n w (mask w) (n * w) Gc = true)
    (hZs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 Z = true)
    (hGs : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 Gc = true)
    (hZo : ordIs n w (mask w) (pidn n w) Z 10 = true)
    (hrel : pcomp n w (mask w) Gc Z = pcomp n w (mask w) Z (pcomp n w (mask w) Z
      (pcomp n w (mask w) Z Gc)))
    (hC : btK n w (mask w) (n * w) BP nb LR TR TRI Z Z = C)
    (hzi : btK n w (mask w) (n * w) BP nb LR TR TRI Z Zi = 0)
    {d : ClsD} {cap : Nat}
    (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList 2 cap [d])
    (hR : d.R = PS 0) {rest : List (List Bool × Nat)} (hpos : ∀ c ∈ rest, 0 < c.2)
    {row₀ row₁ : List Nat} (hL₀ : d.c ≤ row₀.length * 256) (hL₁ : d.c ≤ row₁.length * 256)
    (h₀ : ∀ b < row₀.length, cntZK n w (mask w) (pidn n w) 2 5
      (condWords (([false, true], 11) :: rest)) Z d (b * 256) 256 = row₀.getD b 0)
    (h₁ : ∀ b < row₁.length, cntZK n w (mask w) (pidn n w) 2 5
      (condWords (([false, true], 11) :: rest)) Zi d (b * 256) 256 = row₁.getD b 0) :
    d.c * countPair bs 5 [unpack n w (PS 0)] (([false, true], 11) :: rest)
        (blocksOf n (rawLevels n S base) groups) * C =
      ordK LR nb * (row₀.sum + row₁.sum) := by
  obtain ⟨gA, hA⟩ := exists_perm_of_permOK hpA
  obtain ⟨gB, hB⟩ := exists_perm_of_permOK hpB
  obtain ⟨z₀, hz₀⟩ := exists_perm_of_permOK hpZ
  obtain ⟨g₀, hg₀⟩ := exists_perm_of_permOK hpG
  have hzi₀ : imageList z₀⁻¹ = (unpack n w Zi).toList := invK_rep hz₀ hpZ
  let a : gen2 gA gB := ⟨gA, Subgroup.subset_closure (by simp)⟩
  let z : gen2 gA gB := ⟨z₀, chainS_mem_proved hQ hA hB hnd hz₀ hZc hZs⟩
  let g : gen2 gA gB := ⟨g₀, chainS_mem_proved hQ hA hB hnd hg₀ hGc hGs⟩
  have ha : imageList (a : Equiv.Perm (Fin n)) = (unpack n w (PS 0)).toList := hA
  have hz : imageList (z : Equiv.Perm (Fin n)) = (unpack n w Z).toList := hz₀
  have hzinv : imageList ((z⁻¹ : gen2 gA gB) : Equiv.Perm (Fin n)) = (unpack n w Zi).toList :=
    hzi₀
  have hao : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ordIs_sound hsz hA hAc hAo
  have hzo : orderOf z = 11 := by
    rw [← Subgroup.orderOf_coe]
    exact ordIs_sound hsz hz₀ hZc hZo
  have hgz : g * z * g⁻¹ = z ^ 3 := by
    have e1 := mulK_rep hsz hg₀ hz₀
    have e2 := mulK_rep hsz hz₀ (mulK_rep hsz hz₀ (mulK_rep hsz hz₀ hg₀))
    rw [← hrel, ← e1] at e2
    have e4 : g₀ * z₀ = z₀ * (z₀ * (z₀ * g₀)) := (imageList_inj e2).symm
    have e3 : g * z = z ^ 3 * g := by
      apply Subtype.ext
      change g₀ * z₀ = z₀ ^ 3 * g₀
      rw [e4, pow_three, mul_assoc, mul_assoc]
    rw [e3]
    group
  have hzc : ¬IsConj z z⁻¹ := by
    have hb := btK_proved hQ hA hB hnd hk64 z z⁻¹ hz hzinv
    rw [hzi] at hb
    apply not_isConj_of_card
    convert hb.symm
  have hCz : #(univ.filter fun c : gen2 gA gB => c * z = z * c) = C := by
    rw [← btK_proved hQ hA hB hnd hk64 z z hz hz, hC]
  have hcard : Nat.card (gen2 gA gB) = ordK LR nb := chainS_card_proved hQ hA hB hnd
  have hdvd : ¬11 ^ 2 ∣ Nat.card (gen2 gA gB) := by
    rw [hcard]
    exact hN
  have hR' : imageList (a : Equiv.Perm (Fin n)) = (unpack n w d.R).toList := by
    rw [hR]
    exact hA
  have hcl : #(univ.filter fun x : gen2 gA gB => IsConj a x) = d.c :=
    clsCard_proved hQ hA hB hnd hcls a hR'
  have hpos' : ∀ c ∈ (([false, true], 11) :: rest), 0 < c.2 := by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · decide
    · exact hpos c hc
  have hcp := countPair_proved hQ hA hB hnd hbs hg a ha (by decide : 0 < 5) hpos'
  have hs₀ := cntZK_proved hQ hA hB hnd hcls a hR' z hz (by decide) (by decide) hL₀ h₀
  have hs₁ := cntZK_proved hQ hA hB hnd hcls a hR' z⁻¹ hzinv (by decide) (by decide) hL₁ h₁
  let Q : gen2 gA gB → gen2 gA gB → Prop := fun x y =>
    orderOf y = 5 ∧ ∀ c ∈ rest, orderOf (patP x y c.1) = c.2
  have hQc : ∀ c x y, Q (c * x * c⁻¹) (c * y * c⁻¹) ↔ Q x y := fun c x y => by
    simp only [Q, patP_conj, orderOf_conj']
  have key := pair_total_eleven a Q hQc hdvd hzo hgz hzc
  have hinv : ∀ x : gen2 gA gB, IsConj a x → x ^ (2 - 1) = x ∧ x⁻¹ = x := fun x hx => by
    have h2 : orderOf x = 2 := by
      obtain ⟨c, rfl⟩ := isConj_iff.1 hx
      rw [orderOf_conj', hao]
    refine ⟨pow_one x, ?_⟩
    have hx2 : x ^ 2 = 1 := by
      rw [← h2]
      exact pow_orderOf_eq_one x
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx2)
  have hscan : ∀ u : gen2 gA gB, orderOf u = 11 →
      #(univ.filter fun x : gen2 gA gB => IsConj a x ∧ orderOf (x ^ (2 - 1) * u) = 5 ∧
        ∀ p ∈ condWords (([false, true], 11) :: rest), p.2 = 0 ∨
          orderOf (xyWordP x (x ^ (2 - 1) * u) (x ^ (2 - 1)) ((x ^ (2 - 1) * u) ^ (5 - 1))
            p.1) = p.2) =
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * u)) := fun u hu => by
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    constructor
    · rintro ⟨hx, h5, hw⟩
      obtain ⟨e1, e2⟩ := hinv x hx
      rw [e1] at h5 hw
      refine ⟨hx, by rw [e2]; exact h5, fun c hc => ?_⟩
      have hm : (c.1.map fun b => if b then 1 else 0, c.2) ∈
          condWords (([false, true], 11) :: rest) :=
        List.mem_map_of_mem (f := fun c : List Bool × Nat => (c.1.map fun b => if b then 1 else 0,
          c.2)) (List.mem_cons_of_mem _ hc)
      rcases hw _ hm with h0 | h1
      · exact absurd h0 (Nat.pos_iff_ne_zero.1 (hpos c hc))
      · rw [xyWordP_cond] at h1
        rw [e2]
        exact h1
    · rintro ⟨hx, h5, hr⟩
      obtain ⟨e1, e2⟩ := hinv x hx
      rw [e2] at h5 hr
      refine ⟨hx, by rw [e1]; exact h5, fun p hp => Or.inr ?_⟩
      rw [e1]
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      rw [xyWordP_cond]
      rcases List.mem_cons.1 hc with rfl | hc
      · have hxx : x * x = 1 := by
          nth_rewrite 2 [← e2]
          exact mul_inv_cancel x
        dsimp only
        rw [patP_xy, ← mul_assoc, hxx, one_mul]
        exact hu
      · exact hr c hc
  have hzio : orderOf z⁻¹ = 11 := by
    rw [orderOf_inv]
    exact hzo
  have hcl' : #(univ.filter (IsConj a)) = d.c := hcl
  have hpc : #(univ.filter fun y => orderOf (a * y) = 11 ∧ Q a y) =
      countPair bs 5 [unpack n w (PS 0)] (([false, true], 11) :: rest)
        (blocksOf n (rawLevels n S base) groups) := by
    rw [hcp]
    refine congrArg Finset.card (Finset.filter_congr fun y _ => ?_)
    simp only [Q, List.forall_mem_cons, patP_xy]
    tauto
  have e1 : d.c * countPair bs 5 [unpack n w (PS 0)] (([false, true], 11) :: rest)
        (blocksOf n (rawLevels n S base) groups) * C =
      #(univ.filter (IsConj a)) * #(univ.filter fun y => orderOf (a * y) = 11 ∧ Q a y) *
        #(univ.filter fun c => c * z = z * c) := by
    rw [hcl', hpc, hCz]
  have e2 : Fintype.card (gen2 gA gB) * (#(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) +
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z⁻¹))) =
      ordK LR nb * (row₀.sum + row₁.sum) := by
    rw [Fintype.card_eq_nat_card, hcard, hs₀, hs₁, hscan z hzo, hscan z⁻¹ hzio]
  rw [e1, ← e2]
  convert key

theorem cover_proved (hsz : szOK n w = true)
    (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH) (hnd : base.toList.Nodup)
    (hA : imageList gA = (unpack n w (PS 0)).toList)
    (hB : imageList gB = (unpack n w (PS 1)).toList) {p k mo e : Nat} [Fact p.Prime]
    (hmo : mo = p ^ e) (hmo2 : 2 ≤ mo) (hN : ¬p ^ (k + 1) ∣ ordK LR nb)
    {XL OL JL CL RL : List Nat} (hlen : XL.length = p ^ k) (hinc : incL 0 XL = true)
    (hE : ∀ i < XL.length, eltK n w (mask w) (n * w) (pidn n w) LR TRI BP nb XL RL mo
      (XL.getD i 0) (OL.getD i 0) (JL.getD i 0) (CL.getD i 0) = true)
    (reps : List (gen2 gA gB)) (hRl : reps.length = RL.length)
    (hRi : ∀ j < RL.length, imageList ((reps.getD j 1 : gen2 gA gB) : Equiv.Perm (Fin n)) =
      (unpack n w (RL.getD j 0)).toList) :
    ∀ y : gen2 gA gB, orderOf y = mo → ∃ r ∈ reps, IsConj r y := by
  intro y hy
  have parts : ∀ i < XL.length,
      canonK n w (mask w) (n * w) (XL.getD i 0) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 (XL.getD i 0) = true ∧
      allL (fun Y => memL (pcomp n w (mask w) (XL.getD i 0) Y) XL) XL = true ∧
      ordIs n w (mask w) (pidn n w) (XL.getD i 0) (Nat.pred (OL.getD i 0)) = true ∧
      Bool.rec (motive := fun _ => Bool) true
        (bAnd(Nat.blt (JL.getD i 0) RL.length, bAnd(canonK n w (mask w) (n * w) (CL.getD i 0),
          bAnd(siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 (CL.getD i 0),
            Nat.beq (pcomp n w (mask w) (CL.getD i 0) (RL.getD (JL.getD i 0) 0))
              (pcomp n w (mask w) (XL.getD i 0) (CL.getD i 0))))))
        (Nat.beq (OL.getD i 0) mo) = true := fun i hi => by
    have h := hE i hi
    unfold eltK at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
    exact ⟨h1, h2, h3, h4, h5⟩
  have hex : ∀ i : Fin XL.length, ∃ g : gen2 gA gB,
      imageList (g : Equiv.Perm (Fin n)) = (unpack n w (XL.getD i 0)).toList := fun i =>
    chainS_elem_proved hQ hA hB hnd (parts i i.2).1 (parts i i.2).2.1
  choose el hel using hex
  have hmem : ∀ i : Fin XL.length, XL.getD i 0 ∈ XL := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem i.2
  have hidx : ∀ c ∈ XL, ∃ l : Fin XL.length, XL.getD l 0 = c := fun c hc => by
    obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hc
    exact ⟨⟨l, hl⟩, List.getD_eq_getElem _ _ hl⟩
  have hinj : Function.Injective el := fun i j hij => by
    have e1 : (unpack n w (XL.getD i 0)).toList = (unpack n w (XL.getD j 0)).toList := by
      rw [← hel i, ← hel j, hij]
    have e2 := canonK_inj (parts i i.2).1 (parts j j.2).1 e1
    have hnd := (incL_spec hinc).1.nodup
    rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2] at e2
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e2)
  have hclosed : ∀ x ∈ Set.range el, ∀ z ∈ Set.range el, x * z ∈ Set.range el := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have hc := allL_spec (parts i i.2).2.2.1 _ (hmem j)
    obtain ⟨l, hl⟩ := hidx _ (memL_spec hc)
    refine ⟨l, Subtype.ext (imageList_inj ?_)⟩
    rw [hel l, hl, Subgroup.coe_mul]
    exact (mulK_rep hsz (hel i) (hel j)).symm
  have hne : (Set.range el).Nonempty := by
    have hpos : 0 < XL.length := by
      rw [hlen]
      exact Nat.pos_of_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    exact ⟨el ⟨0, hpos⟩, ⟨_, rfl⟩⟩
  obtain ⟨H, hH⟩ := exists_subgroup_of_closed _ hne hclosed
  have hcardH : Nat.card H = p ^ k := by
    have e1 : Nat.card H = Nat.card (Set.range el) :=
      Nat.card_congr (Equiv.subtypeEquivRight hH)
    rw [e1, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin, hlen]
  have hk : ¬p ^ (k + 1) ∣ Nat.card (gen2 gA gB) := by
    rw [chainS_card_proved hQ hA hB hnd]
    exact hN
  obtain ⟨c, hc⟩ := conj_into_of_card H hcardH hk (y := y) (e := e) (by rw [hy, hmo])
  obtain ⟨i, hi⟩ := (hH _).1 hc
  have hoi : orderOf (el i) = mo := by
    rw [hi, orderOf_conj', hy]
  have hoi' : orderOf ((el i : gen2 gA gB) : Equiv.Perm (Fin n)) =
      Nat.pred (OL.getD i 0) + 1 :=
    ordIs_sound hsz (hel i) (parts i i.2).1 (parts i i.2).2.2.2.1
  rw [Subgroup.orderOf_coe, hoi] at hoi'
  rw [Nat.pred_eq_sub_one] at hoi'
  have hO : OL.getD i 0 = mo := by omega
  have hbr := (parts i i.2).2.2.2.2
  rw [show Nat.beq (OL.getD i 0) mo = true from Nat.beq_eq_true_eq _ _ ▸ hO] at hbr
  obtain ⟨hJ, hbr⟩ := (bAnd_iff _ _).1 hbr
  obtain ⟨hCc, hbr⟩ := (bAnd_iff _ _).1 hbr
  obtain ⟨hCs, hrel⟩ := (bAnd_iff _ _).1 hbr
  have hJ' : JL.getD i 0 < RL.length := by simpa [Nat.blt_eq] using hJ
  obtain ⟨cg, hcg⟩ := chainS_elem_proved hQ hA hB hnd hCc hCs
  set r := reps.getD (JL.getD i 0) 1 with hr
  have hrel' : cg * r = el i * cg := by
    apply Subtype.ext
    apply imageList_inj
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mulK_rep hsz hcg (hRi _ hJ'),
      mulK_rep hsz (hel i) hcg, Nat.eq_of_beq_eq_true hrel]
  refine ⟨r, ?_, ?_⟩
  · rw [hr, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · have h1 : IsConj r (el i) := isConj_iff.2 ⟨cg, by rw [hrel']; group⟩
    have h2 : IsConj y (el i) := isConj_iff.2 ⟨c, hi.symm⟩
    exact h1.trans (isConj_comm.1 h2)

theorem count_one_proved (hsz : szOK n w = true)
    (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH) (hnd : base.toList.Nodup)
    (hpA : permOK n w (mask w) (n * w) (PS 0) (PSI 0) = true)
    (hpB : permOK n w (mask w) (n * w) (PS 1) (PSI 1) = true)
    (hAc : canonK n w (mask w) (n * w) (PS 0) = true) {p k mo e : Nat} [Fact p.Prime]
    (hmo : mo = p ^ e) (hmo2 : 2 ≤ mo)
    (hAo : ordIs n w (mask w) (pidn n w) (PS 0) (mo - 1) = true)
    (hN : ¬p ^ (k + 1) ∣ ordK LR nb) {XL OL JL CL : List Nat} (hlen : XL.length = p ^ k)
    (hinc : incL 0 XL = true)
    (hE : ∀ i < XL.length, eltK n w (mask w) (n * w) (pidn n w) LR TRI BP nb XL [PS 0] mo
      (XL.getD i 0) (OL.getD i 0) (JL.getD i 0) (CL.getD i 0) = true)
    {d : ClsD} {cap : Nat}
    (hcls : ClsOK n w (unpack n w (PS 0)).toList (unpack n w (PS 1)).toList mo cap [d])
    (hR : d.R = PS 0) {bs : List Nat} (hbs : bs = base.toList)
    {groups : List (List Nat)} (hg : groups.flatten = List.range nb) :
    countOrd bs mo (blocksOf n (rawLevels n S base) groups) = d.c := by
  obtain ⟨gA, hA⟩ := exists_perm_of_permOK hpA
  obtain ⟨gB, hB⟩ := exists_perm_of_permOK hpB
  let a : gen2 gA gB := ⟨gA, Subgroup.subset_closure (by simp)⟩
  have hao : orderOf a = mo := by
    rw [← Subgroup.orderOf_coe]
    have := ordIs_sound hsz hA hAc hAo
    rw [this]
    omega
  have hcov := cover_proved hsz hQ hnd hA hB hmo hmo2 hN hlen hinc hE [a] rfl (fun j hj => by
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    exact hA)
  have hcnt := card_order_classes mo [a] (by simpa using hao) (List.pairwise_singleton _ _) hcov
  have hR' : imageList (a : Equiv.Perm (Fin n)) = (unpack n w d.R).toList := by
    rw [hR]
    exact hA
  have hcl := clsCard_proved hQ hA hB hnd hcls a hR'
  rw [countOrd_proved hQ hA hB hnd hbs hg (by omega), ← hcl]
  convert hcnt using 1
  simp

theorem count_two_proved (hsz : szOK n w = true)
    (hQ : ChainS n w PS PSI LR TR TRI kS 2 nb BP S base D NS CH) (hnd : base.toList.Nodup)
    (hk64 : nb ≤ 64)
    (hpA : permOK n w (mask w) (n * w) (PS 0) (PSI 0) = true)
    (hpB : permOK n w (mask w) (n * w) (PS 1) (PSI 1) = true) {p k mo e : Nat} [Fact p.Prime]
    (hmo : mo = p ^ e) (hmo2 : 2 ≤ mo) (hN : ¬p ^ (k + 1) ∣ ordK LR nb)
    {XL OL JL CL : List Nat} {R₁ R₂ C₁ C₂ : Nat} (hlen : XL.length = p ^ k)
    (hinc : incL 0 XL = true)
    (hE : ∀ i < XL.length, eltK n w (mask w) (n * w) (pidn n w) LR TRI BP nb XL [R₁, R₂] mo
      (XL.getD i 0) (OL.getD i 0) (JL.getD i 0) (CL.getD i 0) = true)
    (hc₁ : canonK n w (mask w) (n * w) R₁ = true) (hc₂ : canonK n w (mask w) (n * w) R₂ = true)
    (hs₁ : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 R₁ = true)
    (hs₂ : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 R₂ = true)
    (ho₁ : ordIs n w (mask w) (pidn n w) R₁ (mo - 1) = true)
    (ho₂ : ordIs n w (mask w) (pidn n w) R₂ (mo - 1) = true)
    (hb₁ : btK n w (mask w) (n * w) BP nb LR TR TRI R₁ R₁ = C₁)
    (hb₂ : btK n w (mask w) (n * w) BP nb LR TR TRI R₂ R₂ = C₂) (hne : C₁ ≠ C₂)
    (hp₁ : 0 < C₁) (hp₂ : 0 < C₂) {bs : List Nat} (hbs : bs = base.toList)
    {groups : List (List Nat)} (hg : groups.flatten = List.range nb) :
    countOrd bs mo (blocksOf n (rawLevels n S base) groups) =
      ordK LR nb / C₁ + ordK LR nb / C₂ := by
  obtain ⟨gA, hA⟩ := exists_perm_of_permOK hpA
  obtain ⟨gB, hB⟩ := exists_perm_of_permOK hpB
  obtain ⟨r₁, hr₁⟩ := chainS_elem_proved hQ hA hB hnd hc₁ hs₁
  obtain ⟨r₂, hr₂⟩ := chainS_elem_proved hQ hA hB hnd hc₂ hs₂
  have hro : ∀ (r : gen2 gA gB) (R : Nat), imageList (r : Equiv.Perm (Fin n)) =
      (unpack n w R).toList → canonK n w (mask w) (n * w) R = true →
      ordIs n w (mask w) (pidn n w) R (mo - 1) = true → orderOf r = mo := fun r R h1 h2 h3 => by
    rw [← Subgroup.orderOf_coe, ordIs_sound hsz h1 h2 h3]
    omega
  have hcov := cover_proved hsz hQ hnd hA hB hmo hmo2 hN hlen hinc hE [r₁, r₂] rfl
    (fun j hj => by
      have hj2 : j < 2 := hj
      interval_cases j
      · exact hr₁
      · exact hr₂)
  have hcomm : ∀ (r : gen2 gA gB) (R C : Nat), imageList (r : Equiv.Perm (Fin n)) =
      (unpack n w R).toList →
      btK n w (mask w) (n * w) BP nb LR TR TRI R R = C →
      #(univ.filter fun c : gen2 gA gB => c * r = r * c) = C := fun r R C h1 h3 => by
    rw [← h3, btK_proved hQ hA hB hnd hk64 r r h1 h1]
  have hC₁ := hcomm r₁ R₁ C₁ hr₁ hb₁
  have hC₂ := hcomm r₂ R₂ C₂ hr₂ hb₂
  have hnc : ¬IsConj r₁ r₂ := by
    apply not_isConj_of_comm_card
    convert hne using 2
    · convert hC₁
    · convert hC₂
  have hcnt := card_order_classes mo [r₁, r₂]
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hro _ R₁ hr₁ hc₁ ho₁
      · exact hro _ R₂ hr₂ hc₂ ho₂)
    (by simpa using hnc) hcov
  have hcard : Fintype.card (gen2 gA gB) = ordK LR nb := by
    rw [Fintype.card_eq_nat_card]
    exact chainS_card_proved hQ hA hB hnd
  have hcl : ∀ (r : gen2 gA gB) (C : Nat), 0 < C →
      #(univ.filter fun c : gen2 gA gB => c * r = r * c) = C →
      #(univ.filter (IsConj r)) = ordK LR nb / C := fun r C hC h => by
    have h0 : #(univ.filter (IsConj r)) * #(univ.filter fun c : gen2 gA gB => c * r = r * c) =
        Fintype.card (gen2 gA gB) := by
      convert card_conj_mul_card_comm r
    rw [hcard, h] at h0
    rw [← h0, Nat.mul_div_cancel _ hC]
  rw [countOrd_proved hQ hA hB hnd hbs hg (by omega), hcnt]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact congrArg₂ (· + ·) (by convert hcl r₁ C₁ hp₁ hC₁) (by convert hcl r₂ C₂ hp₂ hC₂)

end CFSG.KS.SporSch.MBT

end
