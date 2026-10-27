module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4FusYCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step47

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow Q47 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native

namespace FusY

structure FusFacts (n : ℕ) (Qg Eg Fg reps : List (Array ℕ)) (zg : Array ℕ) (k₀ : ℕ)
    (Eb : List (Array ℕ)) (KE KF : List (List (Array ℕ))) : Prop where
  eb_ne : permOfArr 64 Eb[k₀]! ≠ 1
  coset : ∀ q ∈ grpN n Qg, permOfArr n Eg[k₀]! * q * (permOfArr n Eg[k₀]! * q) = 1 →
    permOfArr n Eg[k₀]! * q ∈ grpN n (Eg ++ Fg)
  orbit : ∀ i < 2, ∀ j < 2, ∀ v : Fin 64, v ≠ 0 → qv v = 0 →
    ∃ k ∈ grpN 64 (KE[i]! ++ KF[j]!), repV n reps (k v) ∈ grpN n (Eg ++ Fg) ∨
      repV n reps (k v) * permOfArr n zg ∈ grpN n (Eg ++ Fg)
  inv : ∀ i < 2, ∀ j < 2, ∀ k ∈ grpN 64 (KE[i]! ++ KF[j]!), k ≠ 1 → k * k = 1 →
    ∃ g ∈ grpN 64 (KE[i]! ++ KF[j]!), g * k * g⁻¹ = permOfArr 64 Eb[k₀]!

theorem modelFusCheck_parts {n : ℕ} {Qg Eg Fg reps : List (Array ℕ)} {zg : Array ℕ} {k₀ : ℕ}
    {Eb : List (Array ℕ)} {KE KF : List (List (Array ℕ))} {W : List (List ℕ)}
    (h : modelFusCheck n Qg Eg Fg reps zg k₀ Eb KE KF W = true) :
    enumCheckN n (Eg ++ Fg) 256 = true ∧ (!(eqA 64 Eb[k₀]! (idA 64))) = true ∧
      cosetCheck n (eltsN n Qg) Eg[k₀]! (eltsN n (Eg ++ Fg)) = true ∧
      ∀ i < 2, ∀ j < 2,
        orbitCheck (eltsN 64 (KE[i]! ++ KF[j]!)) (codeTab n reps zg (eltsN n (Eg ++ Fg))) = true ∧
          invCheck (eltsN 64 (KE[i]! ++ KF[j]!)) Eb[k₀]! W[2 * i + j]! = true := by
  simp only [modelFusCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem fusFacts_of {n : ℕ} {Qg Eg Fg reps : List (Array ℕ)} {zg : Array ℕ} {k₀ : ℕ}
    {Eb : List (Array ℕ)} {KE KF : List (List (Array ℕ))} {W : List (List ℕ)} {mQ mE : ℕ}
    (hQ : enumCheckN n Qg mQ = true) (hE : enumCheckN n Eg mE = true) (hk₀ : k₀ < Eg.length)
    (hz : validA n zg = true) (hR : RepFacts n Qg reps zg)
    (hK : ∀ i < 2, ∀ j < 2, enumCheckN 64 (KE[i]! ++ KF[j]!) 168 = true)
    (hvEb : validA 64 Eb[k₀]! = true)
    (h : modelFusCheck n Qg Eg Fg reps zg k₀ Eb KE KF W = true) :
    FusFacts n Qg Eg Fg reps zg k₀ Eb KE KF := by
  obtain ⟨hEF, hne, hcos, hall⟩ := modelFusCheck_parts h
  have heg : Eg[k₀]! ∈ Eg := by
    rw [getElem!_pos Eg k₀ hk₀]
    exact List.getElem_mem _
  have hre := rep_of_validA (validA_of_mem hE heg)
  have hrEb := rep_of_validA hvEb
  have hrz := rep_of_validA hz
  refine ⟨fun h1 => ?_, fun q hq hqq => ?_, fun i hi j hj v hv0 hqv => ?_,
    fun i hi j hj k hk hk1 hkk => ?_⟩
  · rw [Bool.not_eq_true'] at hne
    rw [h1] at hrEb
    rw [(eqA_iff hrEb rep_idA).2 rfl] at hne
    exact absurd hne (by decide)
  · obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff hQ).1 hq
    have hc := List.all_eq_true.1 hcos t ht
    rw [Bool.or_eq_true, Bool.not_eq_true'] at hc
    have hr1 := rep_mulN hre hrt
    rcases hc with hc | hc
    · rw [(eqA_iff (rep_mulN hr1 hr1) rep_idA).2 hqq] at hc
      exact absurd hc (by decide)
    · exact mem_of_inLN hEF hc hr1
  · obtain ⟨ho, -⟩ := hall i hi j hj
    have hv := List.all_eq_true.1 ho v.val (List.mem_range.2 v.2)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hv
    have hq0 : q47Form[v.val]! = 0 := hqv
    rcases hv with (hv | hv) | hv
    · exact absurd (Fin.ext hv) hv0
    · exact absurd hq0 hv
    · rw [List.any_eq_true] at hv
      obtain ⟨t, ht, htab⟩ := hv
      have hrt := rep_of_validA (validA_of_mem_elts (hK i hi j hj) ht)
      refine ⟨permOfArr 64 t, (mem_grpN_iff (hK i hi j hj)).2 ⟨t, ht, hrt⟩, ?_⟩
      have htv : t[v.val]! = ((permOfArr 64 t) v).val := hrt.apply v.2
      rw [htv] at htab
      rw [codeTab, getElem!_pos _ _ (by simp), Array.getElem_ofFn, Bool.or_eq_true] at htab
      rcases htab with htab | htab
      · exact Or.inl (mem_of_inLN hEF htab (hR.rep _))
      · exact Or.inr (mem_of_inLN hEF htab (rep_mulN (hR.rep _) hrz))
  · obtain ⟨-, hinv⟩ := hall i hi j hj
    obtain ⟨t, ht, hrt⟩ := (mem_grpN_iff (hK i hi j hj)).1 hk
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem ht
    have hc := List.all_eq_true.1 hinv a (List.mem_range.2 ha)
    rw [getElem!_pos _ a ha] at hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with (hc | hc) | ⟨hwa, hc⟩
    · exact absurd ((eqA_iff hrt rep_idA).1 hc) hk1
    · rw [(eqA_iff (rep_mulN hrt hrt) rep_idA).2 hkk] at hc
      exact absurd hc (by decide)
    · have hgm := List.getElem_mem hwa
      rw [getElem!_pos (eltsN 64 (KE[i]! ++ KF[j]!)) _ hwa] at hc
      have hvg := validA_of_mem_elts (hK i hi j hj) hgm
      refine ⟨permOfArr 64 _, (mem_grpN_iff (hK i hi j hj)).2 ⟨_, hgm, rep_of_validA hvg⟩, ?_⟩
      exact (eqA_iff (rep_conjA hvg hrt) hrEb).1 hc

end FusY

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_sup_zpowers {Q M : Subgroup G} {e : G} (hQM : Q ≤ M)
    (hM : M ≤ Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G)))
    (heM : zpowers e ≤ normalizer (M : Set G)) (hP : IsPGroup 2 (Q ⊔ zpowers e : Subgroup G)) :
    IsSylowOf 2 (Q ⊔ zpowers e) (M ⊔ zpowers e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPW : Q ⊔ zpowers e ≤ M ⊔ zpowers e := sup_le_sup_right hQM _
  obtain ⟨T, hPT, hT⟩ := exists_isSylowOf_ge_of_le hPW hP
  have hTM : T ⊓ M = Q :=
    eq_of_le_sup_oddCoreIn (hT.isPGroup.to_le inf_le_left)
      (le_inf (le_sup_left.trans hPT) hQM) (inf_le_right.trans hM)
  have hTP : T ≤ Q ⊔ zpowers e := by
    intro t ht
    have htW : t ∈ ((zpowers e ⊔ M : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hT.le ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ heM] at htW
    obtain ⟨x, hx, m, hm, rfl⟩ := htW
    have hxT : x ∈ T := hPT (mem_sup_right hx)
    have hmT : m ∈ T := by
      have := T.mul_mem (T.inv_mem hxT) ht
      rwa [inv_mul_cancel_left] at this
    have hmQ : m ∈ Q := hTM ▸ ⟨hmT, hm⟩
    exact mul_mem (mem_sup_right hx) (mem_sup_left hmQ)
  rw [← le_antisymm hTP hPT]
  exact hT

end Sylow

section Proof

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem exists_conj_mul_z (hQ : Sec4Q G A R g E F S₁ Q z) {x : G} (hx : x ∈ Q)
    (hxz : x ∉ zpowers z) : ∃ q ∈ Q, q * x * q⁻¹ = x * z := by
  have hxc : x ∉ centralizer (Q : Set G) := fun h => hxz (hQ.center_Q ▸ ⟨hx, h⟩)
  rw [mem_centralizer_iff] at hxc
  push Not at hxc
  obtain ⟨q, hq, hqx⟩ := hxc
  refine ⟨q, hq, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers hQ.order_z (hQ.commutator_mem hq hx) with h | h
  · exact absurd (by rw [← mul_inv_eq_one, ← h]; group) hqx
  · have hzc : x * z = z * x := mem_centralizer_iff.mp hQ.z_mem_centerIn_Q.2 x hx
    rw [hzc, ← h]
    group

omit [Finite G] in
theorem trS_sup {H : Type} [Group H] {X : Subgroup H} {f : ↥X →* G} {K L : Subgroup H}
    (hK : K ≤ X) (hL : L ≤ X) : trS f (K ⊔ L) = trS f K ⊔ trS f L := by
  rw [trS, trS, trS, subgroupOf_sup hK hL, Subgroup.map_sup]

theorem sec4FusionY_core (hnd : nondegCheck = true) {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)}
    {zg : Array ℕ} {reps NE D Eb Fb : List (Array ℕ)} {KE KF : List (List (Array ℕ))}
    {C : List (Array ℕ)} {U : Subgroup (Equiv.Perm (Fin n))} {k k₀ : ℕ}
    (hMF : ModelFacts n Xg Qg Eg Fg zg reps NE D Eb Fb KE KF C)
    (hFF : FusY.FusFacts n Qg Eg Fg reps zg k₀ Eb KE KF) (hk₀ : k₀ < Eg.length)
    (hm : SylModel (grpN n Xg) (grpN n Qg) (grpN n Eg) (grpN n Fg) U (permOfArr n zg) k)
    (hQ : Sec4Q G A R g E F S₁ Q z) (fN : ↥(grpN n Xg) →* ↥(normalizer (Q : Set G)))
    (hf : Function.Injective ((normalizer (Q : Set G)).subtype.comp fN))
    (hfr : ((normalizer (Q : Set G)).subtype.comp fN).range = S₁)
    (hcS : ∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z)
    (huniq : ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
      (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q)
    (h46 : ∀ X : Subgroup G, X = E ∨ X = F → X ≤ iX z X ∧ Nat.card (iX z X) = 3072 ∧
      iX z X ≤ normalizer (Q : Set G) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3)
    (hzEF : z ∈ E ⊔ F) :
    ∀ y ∈ iX z E ⊔ iX z F, orderOf y = 2 → ∃ h ∈ iX z E ⊔ iX z F, h⁻¹ * y * h ∈ E ⊔ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := std_of_sec4Q hQ
  have hcent := centralizer_le_sup hQ (le_normalizer_of_uniq hQ huniq) hcS
  obtain ⟨hQQ, hzf, hEF⟩ := transport_QZ hm hQ fN hf hfr
  obtain ⟨i, hi, j, hj, hY⟩ := img_Y_eq hnd hMF hm hQ fN hf hfr hcS huniq h46 hQQ hzf hEF
  set c := VCode.ofModel fN hf hMF.rep hm.QX hQQ hm.z_mem hzf with hc
  have hIEN := (h46 E (Or.inl rfl)).2.2.1
  have hIFN := (h46 F (Or.inr rfl)).2.2.1
  have hYN : iX z E ⊔ iX z F ≤ normalizer (Q : Set G) := sup_le hIEN hIFN
  have hEY : E ⊔ F ≤ iX z E ⊔ iX z F :=
    sup_le_sup (h46 E (Or.inl rfl)).1 (h46 F (Or.inr rfl)).1
  have hQY : Q ≤ iX z E ⊔ iX z F :=
    (le_oUpper_of_card (le_inf hQ.Q_le_centralizer hQ.normE) hQ.card).trans le_sup_left
  have hEFm : E ⊔ F = trS ((normalizer (Q : Set G)).subtype.comp fN) (grpN n (Eg ++ Fg)) := by
    rw [grpN_append, trS_sup hm.EX hm.FX]
    rcases hEF with ⟨hE, hF⟩ | ⟨hE, hF⟩
    · rw [hE, hF]
    · rw [hE, hF, sup_comm]
  have hmemEF : ∀ x : ↥(grpN n Xg), (x : Equiv.Perm (Fin n)) ∈ grpN n (Eg ++ Fg) →
      (fN x : G) ∈ E ⊔ F := fun x hx => by
    rw [hEFm]
    exact (apply_mem_trS_iff hf).mpr hx
  have heg : Eg[k₀]! ∈ Eg := by
    rw [getElem!_pos Eg k₀ hk₀]
    exact List.getElem_mem _
  have heX : permOfArr n Eg[k₀]! ∈ grpN n Xg := hm.EX (gen_mem_grpN heg)
  set e : G := (fN ⟨permOfArr n Eg[k₀]!, heX⟩ : G) with hedef
  have heEF : e ∈ E ⊔ F := hmemEF _ (by
    rw [grpN_append]
    exact mem_sup_left (gen_mem_grpN heg))
  have heY : e ∈ iX z E ⊔ iX z F := hEY heEF
  have heN : e ∈ normalizer (Q : Set G) := hYN heY
  have hρe : c.rho hs (fN ⟨permOfArr n Eg[k₀]!, heX⟩) = permOfArr 64 Eb[k₀]! :=
    VCode.rho_eq_of_actsBy (c := c) (hs := hs) (fun v => hm.QX (hMF.rep.mem v)) (fun v => rfl)
      hm.z_mem hzf heX (hMF.actE.2 k₀ hk₀).2
  have hee : e * e = 1 := by
    have h2 : permOfArr n Eg[k₀]! ^ 2 = 1 := hm.elemE.2 _ (gen_mem_grpN heg)
    have h3 : (⟨permOfArr n Eg[k₀]!, heX⟩ : ↥(grpN n Xg)) * ⟨permOfArr n Eg[k₀]!, heX⟩ = 1 :=
      Subtype.ext (by rw [← pow_two]; exact h2)
    show (fN ⟨_, heX⟩ : G) * (fN ⟨_, heX⟩ : G) = 1
    rw [← Subgroup.coe_mul, ← map_mul, h3, map_one]
    rfl
  have hlift : ∀ k ∈ grpN 64 (KE[i]! ++ KF[j]!), ∃ h ∈ iX z E ⊔ iX z F,
      ∃ hh : h ∈ normalizer (Q : Set G), c.rho hs ⟨h, hh⟩ = k := by
    intro k hk
    rw [← hY] at hk
    obtain ⟨⟨h, hh⟩, hhY, rfl⟩ := hk
    exact ⟨h, hhY, hh, rfl⟩
  intro y hy hy2
  have hyy : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
  have hyN := hYN hy
  have hkY : c.rho hs ⟨y, hyN⟩ ∈ grpN 64 (KE[i]! ++ KF[j]!) :=
    hY ▸ VCode.mem_img_of_mem hy hyN
  have hkk : c.rho hs ⟨y, hyN⟩ * c.rho hs ⟨y, hyN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hyN⟩ : ↥(normalizer (Q : Set G))) * ⟨y, hyN⟩ = 1 := Subtype.ext hyy
    rw [this, map_one]
  by_cases hk1 : c.rho hs ⟨y, hyN⟩ = 1
  ·
    have hyQO := (VCode.rho_eq_one_iff hs hnd hcent ⟨y, hyN⟩).1 hk1
    have hP2 : IsPGroup 2 (Q ⊔ zpowers y : Subgroup G) :=
      (VCode.isPGroup_Q hs).to_sup_of_normal_left'
        (AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hyy))
        (zpowers_le.mpr hyN)
    have hyQ : y ∈ Q := by
      have hT := eq_of_le_sup_oddCoreIn hP2 le_sup_left (sup_le le_sup_left (zpowers_le.mpr hyQO))
      rw [← hT]
      exact mem_sup_right (mem_zpowers y)
    by_cases hyz : y = z
    · exact ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one, hyz]; exact hzEF⟩
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    have hyz' : y ∉ zpowers z := by
      rw [VCode.mem_zpowers_iff hs]
      push Not
      exact ⟨hy1, hyz⟩
    have hw0 : c.code y ≠ 0 := fun h => hyz' ((VCode.code_eq_zero_iff hs hyQ).1 h)
    have hqw : qv (c.code y) = 0 := by
      have hsq : c.rep (c.code y) * c.rep (c.code y) = 1 := by
        rcases VCode.code_spec (c := c) hyQ with h1 | h1
        · rw [← h1]
          exact hyy
        · have hzc := hs.z_comm _ (c.rep_mem (c.code y))
          calc c.rep (c.code y) * c.rep (c.code y) =
              (c.rep (c.code y) * z) * (c.rep (c.code y) * z) := by
                rw [show c.rep (c.code y) * z * (c.rep (c.code y) * z) =
                  c.rep (c.code y) * (z * c.rep (c.code y)) * z by group, ← hzc,
                  show c.rep (c.code y) * (c.rep (c.code y) * z) * z =
                    c.rep (c.code y) * c.rep (c.code y) * (z * z) by group, hs.z_sq, mul_one]
            _ = 1 := by rw [← h1]; exact hyy
      rw [VCode.rep_sq] at hsq
      rcases c.qv_eq_zero_or_one (c.code y) with h | h
      · exact h
      · rw [h, pow_one] at hsq
        exact absurd hsq hs.z_ne
    obtain ⟨k, hk, hkw⟩ := hFF.orbit i hi j hj (c.code y) hw0 hqw
    obtain ⟨h, hhY, hhN, rfl⟩ := hlift k hk
    have hy'Q : h * y * h⁻¹ ∈ Q := VCode.conj_mem_Q hhN hyQ
    have hcode : c.code (h * y * h⁻¹) = c.rho hs ⟨h, hhN⟩ (c.code y) :=
      VCode.code_conj hs hhN hyQ
    set w' := c.rho hs ⟨h, hhN⟩ (c.code y) with hw'
    have hw'0 : w' ≠ 0 := by
      intro h0
      apply hw0
      have h00 := (mem_oV.mp (VCode.rho_mem_oV (c := c) hs ⟨h, hhN⟩)).map_zero
      exact (c.rho hs ⟨h, hhN⟩).injective (h0.trans h00.symm)
    have hy'z : h * y * h⁻¹ ∉ zpowers z := fun hm' =>
      hw'0 (hcode ▸ (VCode.code_eq_zero_iff hs hy'Q).2 hm')
    have hrep : c.rep w' ∈ E ⊔ F ∨ c.rep w' * z ∈ E ⊔ F := by
      rcases hkw with h1 | h1
      · exact Or.inl (hmemEF _ h1)
      · right
        have h2 := hmemEF (⟨repV n reps w', hm.QX (hMF.rep.mem w')⟩ * ⟨permOfArr n zg, hm.z_mem⟩)
          h1
        rw [map_mul, Subgroup.coe_mul, ← hzf] at h2
        exact h2
    obtain ⟨q, hq, hqy⟩ := exists_conj_mul_z hQ hy'Q hy'z
    have hzz : ∀ x : G, x * z * z = x := fun x => by rw [mul_assoc, hs.z_sq, mul_one]
    rcases VCode.code_spec (c := c) hy'Q with h1 | h1 <;> rw [hcode] at h1 <;>
      rcases hrep with h2 | h2
    · exact ⟨h⁻¹, inv_mem hhY, by rw [inv_inv, h1]; exact h2⟩
    · refine ⟨(q * h)⁻¹, inv_mem (mul_mem (hQY hq) hhY), ?_⟩
      rw [inv_inv, show (q * h) * y * (q * h)⁻¹ = q * (h * y * h⁻¹) * q⁻¹ by group, hqy, h1]
      exact h2
    · refine ⟨(q * h)⁻¹, inv_mem (mul_mem (hQY hq) hhY), ?_⟩
      rw [inv_inv, show (q * h) * y * (q * h)⁻¹ = q * (h * y * h⁻¹) * q⁻¹ by group, hqy, h1,
        hzz]
      exact h2
    · exact ⟨h⁻¹, inv_mem hhY, by rw [inv_inv, h1]; exact h2⟩
  ·
    obtain ⟨g', hg', hconj⟩ := hFF.inv i hi j hj _ hkY hk1 hkk
    obtain ⟨h, hhY, hhN, rfl⟩ := hlift g' hg'
    have huY : h * y * h⁻¹ ∈ iX z E ⊔ iX z F := mul_mem (mul_mem hhY hy) (inv_mem hhY)
    have huN := hYN huY
    have hρu : c.rho hs ⟨h * y * h⁻¹, huN⟩ = c.rho hs (fN ⟨permOfArr n Eg[k₀]!, heX⟩) := by
      rw [hρe, ← hconj]
      have : (⟨h * y * h⁻¹, huN⟩ : ↥(normalizer (Q : Set G))) =
          ⟨h, hhN⟩ * ⟨y, hyN⟩ * (⟨h, hhN⟩)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    set M := (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))) ⊓ (iX z E ⊔ iX z F) with hMdef
    have heu : e⁻¹ * (h * y * h⁻¹) ∈ M := by
      have heuN : e⁻¹ * (h * y * h⁻¹) ∈ normalizer (Q : Set G) :=
        (normalizer (Q : Set G)).mul_mem ((normalizer (Q : Set G)).inv_mem heN) huN
      refine Subgroup.mem_inf.mpr ⟨(VCode.rho_eq_one_iff (c := c) hs hnd hcent ⟨_, heuN⟩).1 ?_,
        (iX z E ⊔ iX z F).mul_mem ((iX z E ⊔ iX z F).inv_mem heY) huY⟩
      have : (⟨e⁻¹ * (h * y * h⁻¹), heuN⟩ : ↥(normalizer (Q : Set G))) =
          (fN ⟨permOfArr n Eg[k₀]!, heX⟩)⁻¹ * ⟨h * y * h⁻¹, huN⟩ := rfl
      rw [this, map_mul, map_inv, hρu, inv_mul_cancel]
    have hMn : zpowers e ≤ normalizer (M : Set G) := by
      rw [zpowers_le]
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, le_normalizer heY⟩
      exact mem_normalizer_sup_of_mem heN
        (AS76b.normalizer_le_normalizer_oddCoreIn _ (le_normalizer heN))
    have hP2 : IsPGroup 2 (Q ⊔ zpowers e : Subgroup G) :=
      (VCode.isPGroup_Q hs).to_sup_of_normal_left'
        (AS76b.isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hee))
        (zpowers_le.mpr heN)
    have hsyl := isSylowOf_sup_zpowers (le_inf le_sup_left hQY) inf_le_left hMn hP2
    have huW : h * y * h⁻¹ ∈ M ⊔ zpowers e := by
      rw [show h * y * h⁻¹ = e * (e⁻¹ * (h * y * h⁻¹)) by group]
      exact mul_mem (mem_sup_right (mem_zpowers e)) (mem_sup_left heu)
    have huu : (h * y * h⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, show h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ by group, hyy]
      group
    obtain ⟨a, haW, hau⟩ := AS76b.exists_conj_mem_of_isSylowOf hsyl huW huu
    have haY : a ∈ iX z E ⊔ iX z F :=
      (sup_le inf_le_right (zpowers_le.mpr heY) : M ⊔ zpowers e ≤ iX z E ⊔ iX z F) haW
    have haN := hYN haY
    have hu'Q : a * (h * y * h⁻¹) * a⁻¹ ∉ Q := by
      intro hu'
      have h1 := VCode.rho_eq_one_of_mem (c := c) hs ⟨_, hYN (mul_mem (mul_mem haY huY)
        (inv_mem haY))⟩ (mem_sup_left hu')
      have : (⟨a * (h * y * h⁻¹) * a⁻¹, hYN (mul_mem (mul_mem haY huY) (inv_mem haY))⟩ :
          ↥(normalizer (Q : Set G))) = ⟨a, haN⟩ * ⟨h * y * h⁻¹, huN⟩ * (⟨a, haN⟩)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hρu, hρe, mul_inv_eq_one, mul_eq_left] at h1
      exact hFF.eb_ne h1
    have hQe : zpowers e ≤ normalizer (Q : Set G) := zpowers_le.mpr heN
    have hau' : a * (h * y * h⁻¹) * a⁻¹ ∈ ((zpowers e ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hau
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQe] at hau'
    obtain ⟨x, hx, q, hq, hxq⟩ := hau'
    simp only at hxq
    have he1 : e ≠ 1 := by
      intro he
      apply hFF.eb_ne
      rw [← hρe]
      have : fN ⟨permOfArr n Eg[k₀]!, heX⟩ = 1 := Subtype.ext he
      rw [this, map_one]
    have hoe : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hee) he1
    rcases eq_one_or_eq_of_mem_zpowers hoe hx with rfl | rfl
    · exact absurd (hxq ▸ by rw [one_mul]; exact hq) hu'Q
    have hq' := hq
    rw [← hQQ] at hq'
    obtain ⟨qm, hqm, hqmq⟩ := mem_trS.mp hq'
    have hinv : (⟨permOfArr n Eg[k₀]!, heX⟩ * qm) * (⟨permOfArr n Eg[k₀]!, heX⟩ * qm) =
        (1 : ↥(grpN n Xg)) := by
      apply hf
      simp only [map_mul, map_one]
      have h1 : ((normalizer (Q : Set G)).subtype.comp fN) qm = q := hqmq
      have h2 : ((normalizer (Q : Set G)).subtype.comp fN) ⟨permOfArr n Eg[k₀]!, heX⟩ = e := rfl
      rw [h1, h2]
      have := congrArg (fun w => w * w) hxq.symm
      rw [← this, show a * (h * y * h⁻¹) * a⁻¹ * (a * (h * y * h⁻¹) * a⁻¹) =
        (a * h) * (y * y) * (a * h)⁻¹ by group, hyy]
      group
    have hmem := hFF.coset qm hqm (congrArg Subtype.val hinv)
    have hEFu := hmemEF (⟨permOfArr n Eg[k₀]!, heX⟩ * qm) hmem
    rw [map_mul, Subgroup.coe_mul] at hEFu
    have h1 : ((fN qm : ↥(normalizer (Q : Set G))) : G) = q := hqmq
    rw [h1] at hEFu
    refine ⟨(a * h)⁻¹, inv_mem (mul_mem haY hhY), ?_⟩
    rw [inv_inv, show (a * h) * y * (a * h)⁻¹ = a * (h * y * h⁻¹) * a⁻¹ by group, ← hxq]
    exact hEFu

end Proof

namespace FusY

theorem fusYCheck_parts (h : fusYCheck = true) :
    modelFusCheck 16 heSylQ16 heSylE16 heSylF16 q47Rep16 heSylZ16 4 q47Eb16 q47KE16 q47KF16
        fusYWK16 = true ∧
      modelFusCheck 32 heAutQ32 heAutE32 heAutF32 q47Rep32 heAutZ32 1 q47Eb32 q47KE32 q47KF32
        fusYWK32 = true := by
  simp only [fusYCheck, Bool.and_eq_true] at h
  exact h

theorem enumCheck_K_of_modelCheck {n : ℕ} {Xg Qg Eg Fg : List (Array ℕ)} {z : Array ℕ}
    {reps NE D Eb Fb : List (Array ℕ)} {KE KF : List (List (Array ℕ))} {C : List (Array ℕ)}
    (h : modelCheck n Xg Qg Eg Fg z reps NE D Eb Fb KE KF C = true) :
    ∀ i < 2, ∀ j < 2, enumCheckN 64 (KE[i]! ++ KF[j]!) 168 = true := fun i hi j hj =>
  ((modelCheck_parts h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 i hi j hj).1

theorem fusFacts16 (hq47 : q47Check = true)
    (hfus : fusYCheck = true) :
    FusFacts 16 heSylQ16 heSylE16 heSylF16 q47Rep16 heSylZ16 4 q47Eb16 q47KE16 q47KF16 := by
  have h := hq47
  simp only [q47Check, Bool.and_eq_true] at h
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := sylCheck16_parts (sylCheck16_of he_sylowCheck)
  have hMF := modelFacts_of h.1.1.1.1.1 h.1.1.1.2 hX hQ hE hF hvz h.1.2
  exact fusFacts_of hQ hE (by decide) hvz hMF.rep (enumCheck_K_of_modelCheck h.1.2)
    (hMF.actE.2 4 (by decide)).1 (fusYCheck_parts hfus).1

theorem fusFacts32 (hq47 : q47Check = true)
    (hfus : fusYCheck = true) :
    FusFacts 32 heAutQ32 heAutE32 heAutF32 q47Rep32 heAutZ32 1 q47Eb32 q47KE32 q47KF32 := by
  have h := hq47
  simp only [q47Check, Bool.and_eq_true] at h
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := heAutSylowCheck_parts he_autSylowCheck
  have hMF := modelFacts_of h.1.1.1.1.1 h.1.1.1.2 hX hQ hE hF hvz h.2
  exact fusFacts_of hQ hE (by decide) hvz hMF.rep (enumCheck_K_of_modelCheck h.2)
    (hMF.actE.2 1 (by decide)).1 (fusYCheck_parts hfus).2

end FusY

theorem sec4FusionY_of_check
    (hfus : FusY.fusYCheck = true) (h44 : Step44ii)
    (hNX : Sec4NXModel) : Sec4FusionY := by
  intro G _ _ A R g E F S₁ Q z hQ
  obtain ⟨-, hnd, -, -⟩ := Q47.q47Check_parts q47_check
  obtain ⟨-, -, hcS, huniq⟩ := sec4Q_qe h44 hQ
  have h46 : ∀ X : Subgroup G, X = E ∨ X = F → X ≤ iX z X ∧ Nat.card (iX z X) = 3072 ∧
      iX z X ≤ normalizer (Q : Set G) ∧
      ∀ c ∈ iX z X, c ∈ centralizer (Q : Set G) → orderOf c ≠ 3 := by
    intro X hX
    obtain ⟨hXI, ⟨φ, hφ, hker⟩, -, -, hIN, -, h3⟩ := step46_X h44 hNX hQ hX
    refine ⟨hXI, ?_, hIN, h3⟩
    have hX64 : Nat.card X = 64 := by
      rcases hX with rfl | rfl
      exacts [hQ.setting.frame.cardE, hQ.setting.frame.cardF]
    rw [card_eq_card_ker_mul φ hφ, hker, Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv, hX64,
      card_S4Z2]
  have hzE : z ∈ E := by
    obtain ⟨-, -, -, hQE, -⟩ := step46_X h44 hNX hQ (X := E) (Or.inl rfl)
    exact z_mem_of_card hQ hQ.normE hQE
  have hS₁N := le_normalizer_of_uniq hQ huniq
  rcases h44 G A R g E F hQ.setting S₁ hQ.sylowN with ⟨-, P, ⟨e⟩⟩ |
    ⟨-, H, _, _, K, hKn, hK, hi, hC, P, ⟨e⟩⟩
  · obtain ⟨e0⟩ := nonempty_sylow_he_equiv P
    obtain ⟨fN, hf, hfr⟩ := exists_fN hS₁N (e.trans e0).symm
    exact sec4FusionY_core hnd modelFacts16 (FusY.fusFacts16 q47_check hfus) (by decide)
      sylModel16 hQ fN hf hfr hcS huniq h46 (mem_sup_left hzE)
  · obtain ⟨e0⟩ := nonempty_sylow_aut_equiv hKn hK hi hC P
    obtain ⟨fN, hf, hfr⟩ := exists_fN hS₁N (e.trans e0).symm
    exact sec4FusionY_core hnd modelFacts32 (FusY.fusFacts32 q47_check hfus) (by decide)
      sylModel32 hQ fN hf hfr hcS huniq h46 (mem_sup_left hzE)

theorem sec4FusionY_of
    (h44 : Step44ii)
    (hNX : Sec4NXModel) : Sec4FusionY :=
  sec4FusionY_of_check FusY.fusY_check h44 hNX

end CFSG.ComponentClassification.AS81
