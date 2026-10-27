module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Ref

public section

namespace CFSG.ComponentClassification.AS81.Q47

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

section Rep

variable {n : ℕ} {Qg reps : List (Array ℕ)} {z : Array ℕ}

@[expose] noncomputable def repV (n : ℕ) (reps : List (Array ℕ)) (v : Fin 64) :
    Equiv.Perm (Fin n) :=
  permOfArr n reps[v.val]!

structure RepFacts (n : ℕ) (Qg reps : List (Array ℕ)) (z : Array ℕ) : Prop where
  rep : ∀ v : Fin 64, Rep n reps[v.val]! (repV n reps v)
  mem : ∀ v, repV n reps v ∈ grpN n Qg
  zero : repV n reps 0 = 1
  mul : ∀ u v, repV n reps u * repV n reps v = repV n reps (xr u v) ∨
    repV n reps u * repV n reps v = repV n reps (xr u v) * permOfArr n z
  cover : ∀ x ∈ grpN n Qg, ∃ v, x = repV n reps v ∨ x = repV n reps v * permOfArr n z
  sq : ∀ v, (repV n reps v * repV n reps v = 1 ∧ qv v = 0) ∨
    (repV n reps v * repV n reps v = permOfArr n z ∧ qv v = 1)

theorem repCheck_parts (h : repCheck n Qg reps z = true) :
    reps.length = 64 ∧ eqA n reps[0]! (idA n) = true ∧ reps.all (inLN n (eltsN n Qg)) = true ∧
    (∀ u < 64, ∀ v < 64, eqA n (mulN n reps[u]! reps[v]!) reps[u ^^^ v]! = true ∨
      eqA n (mulN n reps[u]! reps[v]!) (mulN n reps[u ^^^ v]! z) = true) ∧
    (∀ x ∈ eltsN n Qg, ∃ v < 64, eqA n x reps[v]! = true ∨ eqA n x (mulN n reps[v]! z) = true) ∧
    ∀ v < 64, (eqA n (mulN n reps[v]! reps[v]!) (idA n) = true ∧ q47Form[v]! = 0) ∨
      (eqA n (mulN n reps[v]! reps[v]!) z = true ∧ q47Form[v]! = 1) := by
  simp only [repCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, List.all_eq_true.2 h3, h4, h5, h6⟩

theorem rep_of_eqA_left {a b : Array ℕ} {g : Equiv.Perm (Fin n)} (hb : Rep n b g)
    (h : eqA n a b = true) : Rep n a g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [this]
  exact hb x

theorem repFacts_of {m : ℕ} (hQ : enumCheckN n Qg m = true) (hz : validA n z = true)
    (h : repCheck n Qg reps z = true) : RepFacts n Qg reps z := by
  obtain ⟨hlen, h0, hin, hmul, hcov, hsq⟩ := repCheck_parts h
  have rz := rep_of_validA hz
  have hrep : ∀ v : Fin 64, Rep n reps[v.val]! (repV n reps v) ∧ repV n reps v ∈ grpN n Qg := by
    intro v
    have hmem : reps[v.val]! ∈ reps := by
      rw [getElem!_pos reps v.val (by omega)]
      exact List.getElem_mem _
    have hi := List.all_eq_true.1 hin _ hmem
    rw [inLN, List.any_eq_true] at hi
    obtain ⟨t, ht, he⟩ := hi
    have hrt := rep_of_validA (validA_of_mem_elts hQ ht)
    have hr : Rep n reps[v.val]! (permOfArr n t) := rep_of_eqA_left hrt he
    have e : repV n reps v = permOfArr n t := permOfArr_eq_of_rep hr
    rw [e]
    exact ⟨hr, (mem_grpN_iff hQ).2 ⟨t, ht, hrt⟩⟩
  refine ⟨fun v => (hrep v).1, fun v => (hrep v).2, ?_, fun u v => ?_, fun x hx => ?_,
    fun v => ?_⟩
  · exact ((eqA_iff (hrep 0).1 rep_idA).1 h0)
  · rcases hmul u.val u.2 v.val v.2 with e | e
    · left
      exact (eqA_iff (rep_mulN (hrep u).1 (hrep v).1) (hrep (xr u v)).1).1 e
    · right
      exact (eqA_iff (rep_mulN (hrep u).1 (hrep v).1) (rep_mulN (hrep (xr u v)).1 rz)).1 e
  · obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hQ).1 hx
    obtain ⟨v, hv, e⟩ := hcov t ht
    rcases e with e | e
    · exact ⟨⟨v, hv⟩, Or.inl ((eqA_iff hrt (hrep ⟨v, hv⟩).1).1 e)⟩
    · exact ⟨⟨v, hv⟩, Or.inr ((eqA_iff hrt (rep_mulN (hrep ⟨v, hv⟩).1 rz)).1 e)⟩
  · rcases hsq v.val v.2 with ⟨e, hq⟩ | ⟨e, hq⟩
    · exact Or.inl ⟨(eqA_iff (rep_mulN (hrep v).1 (hrep v).1) rep_idA).1 e, hq⟩
    · exact Or.inr ⟨(eqA_iff (rep_mulN (hrep v).1 (hrep v).1) rz).1 e, hq⟩

end Rep

section Act

variable {n : ℕ} {Qg reps : List (Array ℕ)} {z : Array ℕ}

@[expose] def ActsBy (n : ℕ) (reps : List (Array ℕ)) (z : Array ℕ) (g : Equiv.Perm (Fin n))
    (d : Equiv.Perm (Fin 64)) : Prop :=
  ∀ v, g * repV n reps v * g⁻¹ = repV n reps (d v) ∨
    g * repV n reps v * g⁻¹ = repV n reps (d v) * permOfArr n z

theorem actsBy_of_imgsOK (hR : RepFacts n Qg reps z) (hz : validA n z = true)
    {gs ds : List (Array ℕ)} (hv : ∀ g ∈ gs, validA n g = true)
    (h : imgsOK n reps z gs ds = true) :
    gs.length = ds.length ∧ ∀ k < gs.length, validA 64 ds[k]! = true ∧
      ActsBy n reps z (permOfArr n gs[k]!) (permOfArr 64 ds[k]!) := by
  simp only [imgsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have hk' := h.2 k hk
  simp only [imgOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hk'
  obtain ⟨hvd, hall⟩ := hk'
  refine ⟨hvd, fun v => ?_⟩
  have hgm : gs[k]! ∈ gs := by
    rw [getElem!_pos gs k hk]
    exact List.getElem_mem _
  have rg := rep_of_validA (hv _ hgm)
  have rd := rep_of_validA hvd
  have hc := rep_conjA (hv _ hgm) (hR.rep v)
  have hdv : (ds[k]!)[v.val]! = (permOfArr 64 ds[k]! v).val := rd.apply v.2
  have hrep' := hR.rep (permOfArr 64 ds[k]! v)
  rw [← hdv] at hrep'
  rcases hall v.val v.2 with e | e
  · exact Or.inl ((eqA_iff hc hrep').1 e)
  · exact Or.inr ((eqA_iff hc (rep_mulN hrep' (rep_of_validA hz))).1 e)

end Act

theorem classCheck_parts {D Eb K₁ K₂ : List (Array ℕ)} (h : classCheck D Eb K₁ K₂ = true) :
    enumCheckN 64 Eb 4 = true ∧ enumCheckN 64 K₁ 24 = true ∧ enumCheckN 64 K₂ 24 = true ∧
    D.all (inLN 64 (eltsN 64 K₁)) = true ∧ D.all (inLN 64 (eltsN 64 K₂)) = true ∧
    oOrd3.all (fun w => !(Eb.all fun e => inLN 64 (eltsN 64 Eb) (conjA 64 w e)) ||
      inLN 64 (eltsN 64 K₁) w || inLN 64 (eltsN 64 K₂) w || enumCheckN 64 (D ++ [w]) 96) =
      true := by
  simp only [classCheck, Bool.and_eq_true, and_assoc] at h
  exact h

theorem eq_cand_of_classCheck (hT : transCheckO = true) {D Eb K₁ K₂ : List (Array ℕ)}
    (h : classCheck D Eb K₁ K₂ = true) (hD : enumCheckN 64 D 8 = true)
    {K : Subgroup (Equiv.Perm (Fin 64))} (hKO : K ≤ oV) (hK : Nat.card K = 24)
    (hDK : grpN 64 D ≤ K) (hKE : K ≤ normalizer (grpN 64 Eb : Set (Equiv.Perm (Fin 64)))) :
    K = grpN 64 K₁ ∨ K = grpN 64 K₂ := by
  obtain ⟨hEb, hK1, hK2, hD1, hD2, hall⟩ := classCheck_parts h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw3⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hK]; norm_num)
  have hwK := w.2
  have hwO := hKO hwK
  have hw3' : orderOf (w : Equiv.Perm (Fin 64)) = 3 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨t, ht, hrt⟩ := exists_mem_oAll hT hwO
  have hvt := validA_of_rep hrt
  have ht3 : t ∈ oOrd3 := by
    refine List.mem_filter.2 ⟨ht, ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(eqA_iff (rep_powN hrt 3) rep_idA).2 (by rw [← hw3']; exact pow_orderOf_eq_one _), ?_⟩
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have := (eqA_iff hrt rep_idA).1 hc
    rw [this, orderOf_one] at hw3'
    exact absurd hw3' (by norm_num)
  have hb := List.all_eq_true.1 hall t ht3
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hb
  set L := grpN 64 D ⊔ zpowers (w : Equiv.Perm (Fin 64)) with hLdef
  have hLK : L ≤ K := sup_le hDK (zpowers_le.mpr hwK)
  have h24 : 24 ∣ Nat.card L := by
    have h8 : 8 ∣ Nat.card L := by
      rw [← card_grpN hD]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h3 : 3 ∣ Nat.card L := by
      rw [← hw3']
      have := Subgroup.card_dvd_of_le (le_sup_right : zpowers (w : Equiv.Perm (Fin 64)) ≤ L)
      rwa [Nat.card_zpowers] at this
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  have hLeq : L = K := Subgroup.eq_of_le_of_card_ge hLK (by
    rw [hK]
    exact Nat.le_of_dvd Nat.card_pos h24)
  have key : ∀ {Kᵢ : List (Array ℕ)}, enumCheckN 64 Kᵢ 24 = true →
      D.all (inLN 64 (eltsN 64 Kᵢ)) = true → inLN 64 (eltsN 64 Kᵢ) t = true → K = grpN 64 Kᵢ := by
    intro Kᵢ hKi hDi hti
    have hwi : (w : Equiv.Perm (Fin 64)) ∈ grpN 64 Kᵢ := mem_of_inLN hKi hti hrt
    have hDi' : grpN 64 D ≤ grpN 64 Kᵢ := grpN_le fun g hg =>
      mem_of_inLN hKi (List.all_eq_true.1 hDi g hg) (rep_of_validA (validA_of_mem hD hg))
    have hLi : L ≤ grpN 64 Kᵢ := sup_le hDi' (zpowers_le.mpr hwi)
    rw [← hLeq]
    exact Subgroup.eq_of_le_of_card_ge hLi (by rw [card_grpN hKi, hLeq, hK])
  rcases hb with ((hb | hb) | hb) | hb
  · exfalso
    have hall' : (Eb.all fun e => inLN 64 (eltsN 64 Eb) (conjA 64 t e)) = true := by
      refine List.all_eq_true.2 fun e he => ?_
      have hve := validA_of_mem hEb he
      have hmem : (w : Equiv.Perm (Fin 64)) * permOfArr 64 e * (w : Equiv.Perm (Fin 64))⁻¹ ∈
          grpN 64 Eb :=
        (mem_normalizer_iff.mp (hKE hwK) _).mp (gen_mem_grpN he)
      have hr := rep_conjA hvt (rep_of_validA hve)
      rw [permOfArr_eq_of_rep hrt] at hr
      exact inLN_of_mem hEb hmem hr
    rw [hall'] at hb
    exact absurd hb (by decide)
  · exact Or.inl (key hK1 hD1 hb)
  · exact Or.inr (key hK2 hD2 hb)
  · exfalso
    have hle : grpN 64 (D ++ [t]) ≤ K := by
      rw [grpN_append]
      refine sup_le hDK (grpN_le fun g hg => ?_)
      rw [List.mem_singleton] at hg
      subst hg
      rw [permOfArr_eq_of_rep hrt]
      exact hwK
    have := Subgroup.card_dvd_of_le hle
    rw [card_grpN hb, hK] at this
    exact absurd this (by norm_num)

structure ModelFacts (n : ℕ) (Xg Qg Eg Fg : List (Array ℕ)) (z : Array ℕ)
    (reps NE D Eb Fb : List (Array ℕ)) (KE KF : List (List (Array ℕ))) (C : List (Array ℕ)) :
    Prop where
  rep : RepFacts n Qg reps z
  ne_card : Nat.card (grpN n NE) = 1024
  ne_le : grpN n NE ≤ grpN n Xg
  ne_normE : grpN n NE ≤ normalizer (grpN n Eg : Set (Equiv.Perm (Fin n)))
  ne_normF : grpN n NE ≤ normalizer (grpN n Fg : Set (Equiv.Perm (Fin n)))
  actD : NE.length = D.length ∧ ∀ k < NE.length, validA 64 D[k]! = true ∧
    ActsBy n reps z (permOfArr n NE[k]!) (permOfArr 64 D[k]!)
  actE : Eg.length = Eb.length ∧ ∀ k < Eg.length, validA 64 Eb[k]! = true ∧
    ActsBy n reps z (permOfArr n Eg[k]!) (permOfArr 64 Eb[k]!)
  actF : Fg.length = Fb.length ∧ ∀ k < Fg.length, validA 64 Fb[k]! = true ∧
    ActsBy n reps z (permOfArr n Fg[k]!) (permOfArr 64 Fb[k]!)
  d_card : Nat.card (grpN 64 D) = 8
  candE : ∀ K : Subgroup (Equiv.Perm (Fin 64)), K ≤ oV → Nat.card K = 24 → grpN 64 D ≤ K →
    K ≤ normalizer (grpN 64 Eb : Set (Equiv.Perm (Fin 64))) →
      K = grpN 64 KE[0]! ∨ K = grpN 64 KE[1]!
  candF : ∀ K : Subgroup (Equiv.Perm (Fin 64)), K ≤ oV → Nat.card K = 24 → grpN 64 D ≤ K →
    K ≤ normalizer (grpN 64 Fb : Set (Equiv.Perm (Fin 64))) →
      K = grpN 64 KF[0]! ∨ K = grpN 64 KF[1]!
  conj : ∀ i < 2, ∀ j < 2, permOfArr 64 C[2 * i + j]! ∈ oV ∧
    ystar.map (MulAut.conj (permOfArr 64 C[2 * i + j]!)).toMonoidHom = grpN 64 (KE[i]! ++ KF[j]!)

theorem modelCheck_parts {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)} {z : Array ℕ}
    {reps NE D Eb Fb : List (Array ℕ)} {KE KF : List (List (Array ℕ))} {C : List (Array ℕ)}
    (h : modelCheck n Xg Qg Eg Fg z reps NE D Eb Fb KE KF C = true) :
    repCheck n Qg reps z = true ∧ enumCheckN n NE 1024 = true ∧
    NE.all (inLN n (eltsN n Xg)) = true ∧
    NE.all (fun g => Eg.all fun q => inLN n (eltsN n Eg) (conjA n g q)) = true ∧
    NE.all (fun g => Fg.all fun q => inLN n (eltsN n Fg) (conjA n g q)) = true ∧
    imgsOK n reps z NE D = true ∧ imgsOK n reps z Eg Eb = true ∧ imgsOK n reps z Fg Fb = true ∧
    enumCheckN 64 D 8 = true ∧ KE.length = 2 ∧ KF.length = 2 ∧
    classCheck D Eb KE[0]! KE[1]! = true ∧ classCheck D Fb KF[0]! KF[1]! = true ∧
    C.length = 4 ∧ C.all isomCheck = true ∧
    ∀ i < 2, ∀ j < 2, enumCheckN 64 (KE[i]! ++ KF[j]!) 168 = true ∧
      q47YGens.all (fun y => inLN 64 (eltsN 64 (KE[i]! ++ KF[j]!)) (conjA 64 C[2 * i + j]! y)) =
        true := by
  simp only [modelCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, List.all_eq_true.2 h3,
    List.all_eq_true.2 fun g hg => List.all_eq_true.2 (h4 g hg),
    List.all_eq_true.2 fun g hg => List.all_eq_true.2 (h5 g hg), h6, h7, h8,
    h9, h10, h11, h12, h13, h14, List.all_eq_true.2 h15, fun i hi j hj =>
      ⟨(h16 i hi j hj).1, List.all_eq_true.2 (h16 i hi j hj).2⟩⟩

theorem modelFacts_of (hT : transCheckO = true) (hq : refCheck = true) {n : ℕ}
    {Xg Qg Eg Fg : List (Array ℕ)} {z : Array ℕ} {reps NE D Eb Fb : List (Array ℕ)}
    {KE KF : List (List (Array ℕ))} {C : List (Array ℕ)} {mX mQ mE mF : ℕ}
    (hX : enumCheckN n Xg mX = true) (hQ : enumCheckN n Qg mQ = true)
    (hE : enumCheckN n Eg mE = true) (hF : enumCheckN n Fg mF = true) (hz : validA n z = true)
    (h : modelCheck n Xg Qg Eg Fg z reps NE D Eb Fb KE KF C = true) :
    ModelFacts n Xg Qg Eg Fg z reps NE D Eb Fb KE KF C := by
  obtain ⟨hrep, hNE, hNX, hnE, hnF, hiD, hiE, hiF, hD, hKE, hKF, hcE, hcF, hC4, hCi, hconj⟩ :=
    modelCheck_parts h
  have hR := repFacts_of hQ hz hrep
  have hvNE : ∀ g ∈ NE, validA n g = true := fun g hg => validA_of_mem hNE hg
  refine ⟨hR, card_grpN hNE, grpN_le_of_all hX hNE hNX, le_normalizer_of_all hE hvNE hnE,
    le_normalizer_of_all hF hvNE hnF, actsBy_of_imgsOK hR hz hvNE hiD,
    actsBy_of_imgsOK hR hz (fun g hg => validA_of_mem hE hg) hiE,
    actsBy_of_imgsOK hR hz (fun g hg => validA_of_mem hF hg) hiF, card_grpN hD,
    fun K hKO hK hDK hKN => eq_cand_of_classCheck hT hcE hD hKO hK hDK hKN,
    fun K hKO hK hDK hKN => eq_cand_of_classCheck hT hcF hD hKO hK hDK hKN,
    fun i hi j hj => ?_⟩
  obtain ⟨hY, -⟩ := refCheck_parts hq
  have hCm : C[2 * i + j]! ∈ C := by
    rw [getElem!_pos C _ (by omega)]
    exact List.getElem_mem _
  have hci := List.all_eq_true.1 hCi _ hCm
  have hcv := (isomCheck_parts hci).1
  obtain ⟨hK, hcy⟩ := hconj i hi j hj
  refine ⟨mem_oV_of_isomCheck hci, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rw [ystar, grpN, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_permsA_iff] at hy
    obtain ⟨ya, hya, rfl⟩ := hy
    have hr := rep_conjA hcv (rep_of_validA (validA_of_mem hY hya))
    exact mem_of_inLN hK (List.all_eq_true.1 hcy ya hya) hr
  · rw [card_grpN hK, card_map_of_injective (MulAut.conj _).injective, card_ystar hq]

end CFSG.ComponentClassification.AS81.Q47
