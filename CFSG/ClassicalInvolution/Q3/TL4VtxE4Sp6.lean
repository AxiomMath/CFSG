module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckC
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import Certificates.Certificate124
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.ComponentClassification.M12Cover CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def K0 : Subgroup (Equiv.Perm (Fin 36)) := Subgroup.closure {rho (), jay ()}

theorem tabs_eq (l : List (Equiv.Perm (Fin 36))) : tabs l = l := by
  rw [tabs]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x _ => tab_eq x

theorem commute_of_isUniqueInvolution {G : Type*} [Group G] {K : Subgroup G} {s : G}
    (h : IsUniqueInvolution K s) {x : G} (hx : x ∈ K) : x * s = s * x := by
  have hmem : x * s * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hx h.mem) (K.inv_mem hx)
  have hsq : x * s * x⁻¹ * (x * s * x⁻¹) = 1 := by
    calc x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  rcases h.unique _ hmem hsq with h1 | h1
  · exfalso
    apply h.ne_one
    calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · calc x * s = (x * s * x⁻¹) * x := by group
      _ = s * x := by rw [h1]

theorem cover_of_centCheck {Q : RawSchreierDatum 36} {cc : ℕ} {gs reps : List (Equiv.Perm (Fin 36))}
    {r : Equiv.Perm (Fin 36)} (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ gs})
    (hreps : ∀ x ∈ reps, ∃ w, x = evalCodes gs w) (h : centCheck Q cc gs reps r = true) :
    ValidSchreier Q ∧ ∀ u ∈ Q.originalSubgroup, orderOf u = 4 →
      ∃ ρ ∈ reps, ∃ d ∈ Q.originalSubgroup, u = d * ρ * d⁻¹ := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  simp only [centCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hQv, -⟩, -⟩, hok⟩, -⟩, h4⟩ := h
  have hgs' : ∀ g ∈ gs, g ∈ Q.originalSubgroup := fun g hg => by
    rw [hQ]
    exact Subgroup.subset_closure hg
  refine ⟨hQv, fun u hu hu4 => ?_⟩
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn Q hQv (listTables_spec hn hgs') 1
    (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh) (by norm_num) reps
    (fun x hx => ⟨by
      rw [inv_one, one_mul]
      obtain ⟨w, rfl⟩ := hreps x hx
      exact evalCodes_mem _ hgs' w,
      (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
        (List.all_eq_true.1 h4 _ (List.mem_map_of_mem hx))⟩) 4000 hok
  exact hcov u (by rwa [inv_one, one_mul]) hu4

theorem ident_at {r : Equiv.Perm (Fin 36)} {Q : RawSchreierDatum 36} {cc : ℕ}
    {gs reps W La Lb : List (Equiv.Perm (Fin 36))} (hcent : centCheck Q cc gs reps r = true)
    (hQ : Q.originalSubgroup = Subgroup.closure {g | g ∈ gs})
    (hreps : ∀ x ∈ reps, ∃ w, x = evalCodes gs w)
    (hCQ : centralizerIn co3X36 r = Q.originalSubgroup)
    (hid : identCheck r reps (enumeration Q) W La Lb = true)
    (hW : ∀ c ∈ W, c ∈ Q.originalSubgroup) {K : Subgroup (Equiv.Perm (Fin 36))}
    (hd : Vtx.AmbientQuatDatum co3X36 K r) :
    ∃ d ∈ co3X36, (∀ x, x ∈ conjSub d K ↔ x ∈ La) ∨ (∀ x, x ∈ conjSub d K ↔ x ∈ Lb) := by
  obtain ⟨hQv, hcov⟩ := cover_of_centCheck hQ hreps hcent
  have hQX : Q.originalSubgroup ≤ co3X36 := by
    rw [← hCQ]
    exact inf_le_left
  have hmemQ : ∀ x ∈ co3X36, x * r = r * x → x ∈ Q.originalSubgroup := fun x hx hxr => by
    rw [← hCQ]
    exact mem_centralizerIn.mpr ⟨hx, hxr⟩
  have hcomQ : ∀ x ∈ Q.originalSubgroup, x * r = r * x := fun x hx => by
    rw [← hCQ] at hx
    exact (mem_centralizerIn.mp hx).2
  obtain ⟨eK⟩ := hd.q8
  set i : Equiv.Perm (Fin 36) := ((eK.symm (QuaternionGroup.a 1) : K) : Equiv.Perm (Fin 36))
    with hi
  have hiK : i ∈ K := (eK.symm (QuaternionGroup.a 1)).2
  have hi4 : orderOf i = 4 := by
    rw [hi, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hii : i * i = r := by
    have h4 : i ^ 4 = 1 := hi4 ▸ pow_orderOf_eq_one i
    have hsq : i * i * (i * i) = 1 := by
      rw [← h4]
      simp [pow_succ, mul_assoc]
    have hne : i * i ≠ 1 := fun h1 => by
      have h2 : orderOf i ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      rw [hi4] at h2
      norm_num at h2
    exact (hd.inv.unique _ (K.mul_mem hiK hiK) hsq).resolve_left hne
  obtain ⟨ρ, hρ, d, hdQ, hid'⟩ :=
    hcov i (hmemQ i (hd.le hiK) (commute_of_isUniqueInvolution hd.inv hiK)) hi4
  have hdX : d ∈ co3X36 := hQX hdQ
  have hdr := hcomQ d hdQ
  have hd₂ := hd.conj (co3X36.inv_mem hdX)
  have e1 : d⁻¹ * r * d⁻¹⁻¹ = r := by
    calc d⁻¹ * r * d⁻¹⁻¹ = d⁻¹ * (r * d) := by group
      _ = d⁻¹ * (d * r) := by rw [hdr]
      _ = r := by group
  rw [e1] at hd₂
  have hρK : ρ ∈ conjSub d⁻¹ K := by
    have h1 := conj_mem_conjSub (n := d⁻¹) hiK
    rwa [hid', show d⁻¹ * (d * ρ * d⁻¹) * d⁻¹⁻¹ = ρ by group] at h1
  have hρr : ρ * ρ = r := by
    rw [hid'] at hii
    calc ρ * ρ = d⁻¹ * (d * ρ * d⁻¹ * (d * ρ * d⁻¹)) * d := by group
      _ = d⁻¹ * (r * d) := by rw [hii]; group
      _ = d⁻¹ * (d * r) := by rw [hdr]
      _ = r := by group
  refine ⟨d⁻¹, co3X36.inv_mem hdX, eq_of_identCheck hd₂ hid ?_ ?_ hρ hρK hρr⟩
  · intro j hj hjr
    rw [mem_enumeration_iff Q hQv]
    exact hmemQ j hj hjr
  · intro c hc
    exact ⟨hQX (hW c hc), hcomQ c (hW c hc)⟩


theorem check_parts : rho () * rho () = tab sp6Rep2 ∧ closedL (L0 ()) (rho ()) (jay ()) = true ∧
    identCheck sp6Rep1 sp6FourReps1 (enumeration sp6CentQ1) [] [] [] = true ∧
    identCheck sp6Rep2 sp6FourReps2 (enumeration sp6CentQ2) (W ()) (L0 ()) (L1 ()) = true ∧
    identCheck sp6Rep3 sp6FourReps3 (enumeration sp6CentQ3) [] [] [] = true ∧
    identCheck sp6Rep4 sp6FourReps4 (enumeration sp6CentQ4) [] [] [] = true ∧
    memberCheck sp6Gens (L0 ()) (rho ()) (jay ()) (ws ()) memberSigma = true ∧
    treeCheck (L0 ()) (U ()) (rho ()) (jay ()) (ws ()) memberTree = true ∧
    nbrCheck (L0 ()) (rho ()) (jay ()) (ws ()) [0, 11] = true ∧
    edgeCheck (L0 ()) (rho ()) (jay ()) (twin ()) = true := by
  have h := Certificates.certificate124
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  rw [tab_eq, tabs_eq] at h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem mem_K0_iff (x : Equiv.Perm (Fin 36)) : x ∈ K0 ↔ x ∈ L0 () :=
  mem_closure_iff check_parts.2.1 (q8Elems_sub check_parts.1) x

theorem ws_mem
    (k : ℕ) : (ws ()).getD k 1 ∈ co3X36 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (ws ())[k]? with
  | none => exact co3X36.one_mem
  | some g =>
    have hg := List.mem_of_getElem? h
    rw [ws, List.mem_map] at hg
    obtain ⟨w, -, rfl⟩ := hg
    rw [Option.getD_some, tab_eq, ← sp6Q_originalSubgroup]
    exact evalCodes_mem _ sp6Gens_mem w

theorem co3X36_eq_closure :
    co3X36 = Subgroup.closure {g | g ∈ sp6Gens} := by
  rw [← sp6Q_originalSubgroup, sp6Q, certificate_originalSubgroup]


theorem ident_ambient {K : Subgroup (Equiv.Perm (Fin 36))} {s : Equiv.Perm (Fin 36)}
    (hd : Vtx.AmbientQuatDatum co3X36 K s) : ∃ g ∈ co3X36, conjSub g K = K0 := by
  obtain ⟨-, -, h1, h2, h3, h4, -, -, -, -⟩ := check_parts
  have hsX : s ∈ co3X36 := hd.le hd.inv.mem
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hd.inv.sq) hd.inv.ne_one
  obtain ⟨r, hr, c, hc, rfl⟩ := co3X36_involution_centralizers.1 s hsX hs2
  have hd₁ := hd.conj (co3X36.inv_mem hc)
  rw [show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group] at hd₁
  have hCQ : ∀ (r' : Equiv.Perm (Fin 36)) (Q : RawSchreierDatum 36),
      centralizerIn sp6Q.originalSubgroup r' = Q.originalSubgroup →
        centralizerIn co3X36 r' = Q.originalSubgroup := fun r' Q h => by
    rwa [← sp6Q_originalSubgroup]
  have hempty : ∀ d, ¬ ((∀ x, x ∈ conjSub d (conjSub c⁻¹ K) ↔
      x ∈ ([] : List (Equiv.Perm (Fin 36)))) ∨
      (∀ x, x ∈ conjSub d (conjSub c⁻¹ K) ↔ x ∈ ([] : List (Equiv.Perm (Fin 36))))) := by
    intro d h
    rcases h with h | h <;> exact List.not_mem_nil ((h 1).mp (Subgroup.one_mem _))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨d, -, hdK⟩ := ident_at sp6_cent_check₁ (by rw [sp6CentQ1, certificate_originalSubgroup])
      exists_word_of_mem_map (hCQ _ _ sp6_cent_spec₁.1) h1 (by simp) hd₁
    exact absurd hdK (hempty d)
  · have hW : ∀ c ∈ W (), c ∈ sp6CentQ2.originalSubgroup := by
      intro c hc
      simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hc
      rw [hc, tab_eq, sp6CentQ2, certificate_originalSubgroup]
      refine Subgroup.subset_closure ?_
      rw [List.getD_eq_getElem _ _ (by simp [sp6CentGens2])]
      exact List.getElem_mem _
    obtain ⟨d, hdX, hdK⟩ := ident_at sp6_cent_check₂
      (by rw [sp6CentQ2, certificate_originalSubgroup]) exists_word_of_mem_map
      (hCQ _ _ sp6_cent_spec₂.1) h2 hW hd₁
    rcases hdK with hdK | hdK
    · refine ⟨d * c⁻¹, co3X36.mul_mem hdX (co3X36.inv_mem hc), ?_⟩
      ext x
      rw [conjSub_mul, hdK, mem_K0_iff]
    · refine ⟨(twin ())⁻¹ * d * c⁻¹,
        co3X36.mul_mem (co3X36.mul_mem (co3X36.inv_mem (ws_mem 11)) hdX)
        (co3X36.inv_mem hc), ?_⟩
      ext x
      rw [conjSub_mul, conjSub_mul, mem_conjSub_iff, inv_inv, hdK, mem_K0_iff, L1, List.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := by
          have h5 := congrArg (fun z => (twin ())⁻¹ * z * twin ()) hyx
          simpa [mul_assoc] using h5
        rwa [← hxy]
      · intro hx
        exact ⟨x, hx, rfl⟩
  · obtain ⟨d, -, hdK⟩ := ident_at sp6_cent_check₃ (by rw [sp6CentQ3, certificate_originalSubgroup])
      exists_word_of_mem_map (hCQ _ _ sp6_cent_spec₃.1) h3 (by simp) hd₁
    exact absurd hdK (hempty d)
  · obtain ⟨d, -, hdK⟩ := ident_at sp6_cent_check₄ (by rw [sp6CentQ4, certificate_originalSubgroup])
      exists_word_of_mem_map (hCQ _ _ sp6_cent_spec₄.1) h4 (by simp) hd₁
    exact absurd hdK (hempty d)

theorem ws_zero : (ws ()).getD 0 1 = 1 := by
  have h := check_parts.2.2.2.2.2.2.1
  simp only [memberCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem exists_member {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) :
    ∃ k < (ws ()).length, conjSub g K0 = conjSub ((ws ()).getD k 1) K0 :=
  exists_member_of_memberCheck mem_K0_iff check_parts.2.2.2.2.2.2.1 (co3X36_eq_closure ▸ hg)

theorem reflTransGen_starRel {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) :
    Relation.ReflTransGen (Vtx.StarRel co3X36 K0) K0 (conjSub g K0) := by
  obtain ⟨k, hk, he⟩ := exists_member hg
  rw [he]
  exact reflTransGen_of_treeCheck mem_K0_iff (fun k _ => ws_mem k) ws_zero
    check_parts.2.2.2.2.2.2.2.1 k hk

theorem eq_twin_of_le_normalizer {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36)
    (hne : conjSub g K0 ≠ K0) (hle : conjSub g K0 ≤ Subgroup.normalizer (K0 : Set _)) :
    conjSub g K0 = conjSub (twin ()) K0 := by
  obtain ⟨k, hk, he⟩ := exists_member hg
  rw [he] at hne hle ⊢
  by_cases hk0 : k = 0
  · subst hk0
    rw [ws_zero, conjSub_one] at hne
    exact absurd rfl hne
  by_cases hk11 : k = 11
  · subst hk11
    rfl
  · exact absurd hle (not_le_normalizer_of_nbrCheck mem_K0_iff check_parts.2.2.2.2.2.2.2.2.1 hk
      (by simp [hk0, hk11]))

theorem edge : conjSub (twin ()) K0 ≠ K0 ∧
    conjSub (twin ()) K0 ≤ Subgroup.normalizer (K0 : Set _) :=
  edge_of_edgeCheck mem_K0_iff check_parts.2.2.2.2.2.2.2.2.2

section Model

variable {M : Type} [Group M] (e : M ≃* ↥co3X36)

@[expose] noncomputable def emb : M →* Equiv.Perm (Fin 36) := co3X36.subtype.comp e.toMonoidHom

theorem emb_injective : Function.Injective (emb e) :=
  Subtype.val_injective.comp e.injective

theorem range_emb : (emb e).range = co3X36 := by
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    exact (e m).2
  · intro hg
    exact ⟨e.symm ⟨g, hg⟩, by simp [emb]⟩

theorem sp62QuatIdent {K : Subgroup M} {s : M} (hd : QuatTwinDatum K s) :
    ∃ m : M, conjSub (emb e m) (K.map (emb e)) = K0 := by
  have had := Vtx.ambientQuatDatum_map (emb e) (emb_injective e) hd
  rw [range_emb] at had
  obtain ⟨g, hg, hgK⟩ := ident_ambient had
  rw [← range_emb e] at hg
  obtain ⟨m, rfl⟩ := hg
  exact ⟨m, hgK⟩

end Model

theorem e4QuatGraphFacts_PSp {M : Type} [Group M] [Finite M]
    (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4QuatGraphFacts M := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  have hmem : ∀ m : M, emb e m ∈ co3X36 := fun m => (e m).2
  refine Vtx.e4QuatGraphFacts_of_model co3X36 K0 [conjSub (twin ()) K0] (by simp)
    (fun K s hd => ?_) ⟨twin (), ws_mem 11, edge⟩ (fun h hh => reflTransGen_starRel hh)
    (fun h hh hne hle => by
      rw [eq_twin_of_le_normalizer hh hne hle]
      exact List.mem_singleton_self _)
  obtain ⟨m, hm⟩ := sp62QuatIdent e hd
  refine ⟨(MulAut.conj (emb e m)).toMonoidHom.comp (emb e),
    (MulAut.conj (emb e m)).injective.comp (emb_injective e), ?_, ?_⟩
  · rw [MonoidHom.range_comp, range_emb]
    exact conjSub_eq_self_of_mem (hmem m)
  · rw [← Subgroup.map_map]
    exact hm

end CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
