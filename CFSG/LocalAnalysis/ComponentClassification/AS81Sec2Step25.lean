module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem sec2P_sup_sec2S_le_normalizer_sec2Z :
    sec2P E ⊔ sec2S A R E F ≤ normalizer (sec2Z A E F : Set G) := by
  rw [← centerIn_sec2S_eq h11 hE16 hF hL hodd]
  exact sup_le (fun p hp => mem_normalizer_centerIn
    (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd hp))
    fun s hs => mem_normalizer_centerIn (le_normalizer hs)

theorem inf_le_centralizerMod_sec2P_sup :
    E ⊓ A ≤ centralizerMod (sec2P E ⊔ sec2S A R E F) (sec2P E ⊔ sec2S A R E F) (sec2Z A E F) := by
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hPS := sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd
  obtain ⟨hES, -⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  intro e he
  refine mem_centralizerMod.mpr ⟨mem_sup_right (hES he.1),
    sec2P_sup_sec2S_le_normalizer_sec2Z h11 hE16 hF hL hodd (mem_sup_right (hES he.1)),
    fun w hw => ?_⟩
  have hw' : w ∈ ((sec2P E ⊔ sec2S A R E F : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hPS] at hw'
  obtain ⟨p, hp, s, hs, rfl⟩ := hw'
  have hpe : p * e = e * p := (mem_centralizer_iff.mp (hPC hp) e he).symm
  have h1 := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd ((sec2S A R E F).inv_mem hs)
    ((sec2S A R E F).inv_mem (hES he.1))).2
  have h2 : (p * s)⁻¹ * e⁻¹ * (p * s) * e = s⁻¹ * e⁻¹ * s⁻¹⁻¹ * e⁻¹⁻¹ := by
    calc (p * s)⁻¹ * e⁻¹ * (p * s) * e = s⁻¹ * (p⁻¹ * e⁻¹ * p) * s * e := by group
      _ = s⁻¹ * e⁻¹ * s * e := by
          rw [show p⁻¹ * e⁻¹ * p = e⁻¹ by
            have hc : p * e⁻¹ = e⁻¹ * p := ((Commute.inv_right (hpe : Commute p e))).eq
            rw [mul_assoc, ← hc, inv_mul_cancel_left]]
      _ = s⁻¹ * e⁻¹ * s⁻¹⁻¹ * e⁻¹⁻¹ := by rw [inv_inv, inv_inv]
  rw [h2]
  exact h1

theorem centralizerMod_sec2P_sup_le :
    centralizerMod (sec2P E ⊔ sec2S A R E F) (sec2P E ⊔ sec2S A R E F) (sec2Z A E F) ≤
      centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
  have hZF : sec2Z A E F ≤ F := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_right
  have hFE := hF.F_le_normalizer hL hodd
  have hFP : F ≤ normalizer (sec2P E : Set G) := hFE.trans (Sec2.normalizer_le_normalizer_sec2P E)
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hPSF : sec2P E ⊔ sec2S A R E F = sec2P E ⊔ F :=
    le_antisymm (sup_le le_sup_left (sup_le le_sup_right
      fun c hc => mem_sup_left (mem_centralizerMod.mp hc).1)) (sup_le le_sup_left
      ((le_sup_left : F ≤ sec2S A R E F).trans le_sup_right))
  intro x hx
  obtain ⟨hxPS, -, hxc⟩ := mem_centralizerMod.mp hx
  have hx' : x ∈ ((sec2P E ⊔ F : Subgroup G) : Set G) := hPSF ▸ hxPS
  rw [coe_mul_of_right_le_normalizer_left _ F hFP] at hx'
  obtain ⟨p, hp, f, hf, rfl⟩ := hx'
  have hfQ : ∀ t ∈ sec2P E, f ∈ normalizer (rightConjugate R t : Set G) := fun t ht => by
    have h1 := hxc t (mem_sup_left ht)
    have he₂ := (hD.sq_mem_and_commutator_mem hT hCE (inv_mem ht) (inv_mem hp)).2
    have hv : t⁻¹ * f⁻¹ * t * f ∈ E := by
      have h2 : t⁻¹ * f⁻¹ * t * f = t⁻¹ * (p * f)⁻¹ * t * (p * f) *
          (f⁻¹ * (t⁻¹ * p⁻¹ * t⁻¹⁻¹ * p⁻¹⁻¹) * f)⁻¹ := by group
      rw [h2]
      exact E.mul_mem (hZE h1) (E.inv_mem ((mem_normalizer_iff.mp (hFE (F.inv_mem hf)) _).mp
        he₂ |> fun h => by simpa [mul_assoc] using h))
    suffices hf' : f⁻¹ ∈ normalizer (rightConjugate R t : Set G) by simpa using inv_mem hf'
    refine Sec2.mem_normalizer_of_forall_conj_mem fun q hq => ?_
    rw [inv_inv]
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ R, t⁻¹ * r * t = q :=
      ⟨t * q * t⁻¹, (mem_rightConjugate_iff R t q).mp hq, by group⟩
    have hrf : f * r = r * f := hFc f hf r (hF.R_le_F hr)
    have hqE : t⁻¹ * r * t ∈ E := by
      have := (mem_normalizer_iff.mp (Sec2.sec2P_le E (inv_mem ht)) r).mp (hF.R_le_E hr)
      simpa using this
    have hcomm := hD.comm _ hv _ hqE
    have key : f⁻¹ * (t⁻¹ * r * t) * f =
        (t⁻¹ * f⁻¹ * t * f)⁻¹ * (t⁻¹ * r * t) * (t⁻¹ * f⁻¹ * t * f) := by
      calc f⁻¹ * (t⁻¹ * r * t) * f = (t⁻¹ * f⁻¹ * t * f)⁻¹ * t⁻¹ * (f⁻¹ * r * f) * t *
            (t⁻¹ * f⁻¹ * t * f) := by group
        _ = (t⁻¹ * f⁻¹ * t * f)⁻¹ * (t⁻¹ * r * t) * (t⁻¹ * f⁻¹ * t * f) := by
            rw [show f⁻¹ * r * f = r by rw [mul_assoc, ← hrf, inv_mul_cancel_left]]
            group
    rw [key, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    exact (mem_rightConjugate_iff R t _).mpr (by group; exact hr)
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hQ : rightConjugate R h ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (Sec2.sec2P_le E hh)
  have hQEF : ¬ rightConjugate R h ≤ E ⊓ F := fun hle =>
    hhC (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hh hle)
  have hfE := mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd hf hQ hQEF (hfQ h hh)
  have hxP : p * f ∈ sec2P E :=
    (sec2P E).mul_mem hp (Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer
      le_rfl hfE)
  have hxF : p * f ∈ normalizer (F : Set G) := by
    have h1 : (p * f)⁻¹ ∈ normalizer (F : Set G) := Sec2.mem_normalizer_of_forall_conj_mem
      fun f' hf' => by
        have h2 := hxc f' (mem_sup_right ((le_sup_left : F ≤ sec2S A R E F) hf'))
        have h3 : (p * f)⁻¹ * f' * (p * f)⁻¹⁻¹ =
            f' * (f'⁻¹ * (p * f)⁻¹ * f' * (p * f)) := by group
        rw [h3]
        exact F.mul_mem hf' (hZF h2)
    simpa using inv_mem h1
  rw [← sec2P_inf_normalizer_F_eq h11 hE16 hF hL hodd]
  exact ⟨hxP, hxF⟩

theorem mem_of_conj_mem_of_torus {y : G} (hyA : y ∈ A) (hyfix : ∀ w ∈ E ⊓ F ⊓ A,
    y * w * y⁻¹ = w → w = 1) {c : G}
    (hc : c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
    (hcy : c⁻¹ * (y * c * y⁻¹) ∈ E) : c ∈ E := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨-, -, hCEF⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hcP := (mem_centralizerMod.mp hc).1
  have hREF : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  set Q := rightConjugate R c with hQ
  have hQEF : Q ≤ E ⊓ F := by
    rw [hQ, ← (rightConjugate_eq_self_iff _ c).mpr (hCEF hc)]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hREF c
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ = q := fun q hq => by
    have hr : c * q * c⁻¹ ∈ R := (mem_rightConjugate_iff R c q).mp hq
    have hyr : y * (c * q * c⁻¹) * y⁻¹ = c * q * c⁻¹ := by
      rw [mem_centralizer_iff.mp (hRA hr) y hyA, mul_inv_cancel_right]
    have hcomm := hD.comm _ hcy _ (hQEF hq).1
    calc y * q * y⁻¹ = (c⁻¹ * (y * c * y⁻¹))⁻¹ * (c⁻¹ * (y * (c * q * c⁻¹) * y⁻¹) * c) *
          (c⁻¹ * (y * c * y⁻¹)) := by group
      _ = (c⁻¹ * (y * c * y⁻¹))⁻¹ * q * (c⁻¹ * (y * c * y⁻¹)) := by rw [hyr]; group
      _ = q := by rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hZN : sec2Z A E F ≤ normalizer (R : Set G) := fun z hz =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      hD.comm r (hD.R_le hr) z (hF.sec2Z_eq ▸ hz : z ∈ E ⊓ F ⊓ A).1.1)
  have hQR : Q ≤ R := fun q hq => by
    have hq' : q ∈ ((R ⊔ sec2Z A E F : Subgroup G) : Set G) := by
      rw [hF.sup_sec2Z]
      exact hQEF hq
    rw [coe_mul_of_right_le_normalizer_left R _ hZN] at hq'
    obtain ⟨r, hr, z, hz, rfl⟩ := hq'
    have hyr : y * r * y⁻¹ = r := by
      rw [mem_centralizer_iff.mp (hRA hr) y hyA, mul_inv_cancel_right]
    have hz1 : z = 1 := by
      refine hyfix z (hF.sec2Z_eq ▸ hz) ?_
      have h1 := hyQ _ hq
      have h2 : y * (r * z) * y⁻¹ = (y * r * y⁻¹) * (y * z * y⁻¹) := by group
      rw [h2, hyr] at h1
      exact mul_left_cancel h1
    show r * z ∈ R
    rw [hz1, mul_one]
    exact hr
  have hQeq : Q = R := eq_of_le_of_card_ge hQR (by rw [hQ, rightConjugate_card])
  have hcR : c ∈ normalizer (R : Set G) := (rightConjugate_eq_self_iff R c).mp hQeq
  rw [← sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)]
  exact ⟨hcP, hcR⟩

theorem eq_one_of_mem_R_of_mem_centralizerMod {r : G} (hr : r ∈ R)
    (hrD : r ∈ centralizerMod (sec2P E ⊔ sec2S A R E F) (sec2P E ⊔ sec2S A R E F)
      (sec2Z A E F)) : r = 1 := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hQ : rightConjugate R h ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (Sec2.sec2P_le E hh)
  have hQEF : ¬ rightConjugate R h ≤ E ⊓ F := fun hle =>
    hhC (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hh hle)
  have hbot := inf_eq_bot_of_not_le_inf h11 hE16 hF hL hodd hQ hQEF
  have h1 := (mem_centralizerMod.mp hrD).2.2 h (mem_sup_left hh)
  have hmem : h⁻¹ * r * h ∈ rightConjugate R h ⊓ (E ⊓ F) := by
    refine ⟨(mem_rightConjugate_iff R h _).mpr (by group; exact hr), ?_⟩
    rw [← hF.sup_sec2Z]
    have h2 : h⁻¹ * r * h = r * (h⁻¹ * r⁻¹ * h * r)⁻¹ := by group
    rw [h2]
    exact mul_mem (mem_sup_left hr) (mem_sup_right (inv_mem h1))
  rw [hbot, mem_bot] at hmem
  have : r = h * (h⁻¹ * r * h) * h⁻¹ := by group
  rw [this, hmem, mul_one, mul_inv_cancel]

theorem centralizerMod_sec2F0_eq {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G}
    (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    centralizerMod (sec2F0 A E x) (sec2P E) (sec2Z A E F) = E ⊓ A := by
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have hhS' : h ∉ sec2S A R F E := hSc ▸ hhS
  have hxS' : x ∉ sec2S A R F E := hSc ▸ hxS
  set F₀ := sec2F0 A E x with hF₀
  set F₀' := sec2F0 A F h with hF₀'
  set M := centralizerMod F₀ (sec2P E) (sec2Z A E F) with hM
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hZEA : sec2Z A E F ≤ E ⊓ A := by
    rw [hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have hEAM : E ⊓ A ≤ M := fun e he => mem_centralizerMod.mpr ⟨mem_sup_left he,
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨z, (hZEA hz).1⟩ ⟨e, he.1⟩)),
    fun p hp => by
      have hpe : p * e = e * p := (mem_centralizer_iff.mp (hPC hp) e he).symm
      have h1 : p⁻¹ * e⁻¹ * p * e = 1 := by
        calc p⁻¹ * e⁻¹ * p * e = p⁻¹ * e⁻¹ * (p * e) := by group
          _ = p⁻¹ * e⁻¹ * (e * p) := by rw [hpe]
          _ = 1 := by group
      rw [h1]
      exact one_mem _⟩
  have hMF : M ≤ F₀ := fun m hm => (mem_centralizerMod.mp hm).1
  have hF₀C : F₀ ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd, inf_comm]
    exact sec2F0_le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  have hyZ := (mem_normalizer_sec2S_of_mem hF hyA hyE hyF).1
  have hyF₀ := mem_normalizer_sec2F0_of_mem h11 hE16 hF hL hodd hyA hyE hyF hx hxS
  have hyM : y ∈ normalizer (M : Set G) :=
    Sec2.mem_normalizer_centralizerMod hyF₀ (Sec2.normalizer_le_normalizer_sec2P E hyE) hyZ
  have hyEA : y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, le_normalizer hyA⟩
  have hidxF : (E ⊓ A).relIndex F₀ = 4 := by
    have h1 := relIndex_mul_card (E ⊓ A) F₀
    rw [inf_eq_left.mpr (show E ⊓ A ≤ F₀ from le_sup_left), card_inf_left hF hodd,
      card_sec2F0 h11 hE16 hF hL hodd hx hxS] at h1
    omega
  have hidx := relIndex_mul_relIndex (E ⊓ A) M F₀ hEAM hMF
  rw [hidxF] at hidx
  have hMne : M.relIndex F₀ ≠ 1 := by
    intro h1
    have hF₀M : F₀ ≤ M := relIndex_eq_one.mp h1
    have hEH := conjSet_E_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
    have hFH := conjSet_F_sec2H_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
    have hF₀mem : F₀ ∈ conjSet F (sec2H E F) := by rw [hFH]; exact Set.mem_insert _ _
    have hF₀'mem : F₀' ∈ conjSet E (sec2H E F) := by rw [hEH]; exact Set.mem_insert _ _
    have hcross := (inf_eq_sec2Z_and_card_inf h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
      hF₀mem).2 F₀' hF₀'mem
    have hHc : sec2H F E = sec2H E F := sup_comm _ _
    have hF₀'mem' : F₀' ∈ conjSet E (sec2H F E) := by rw [hHc]; exact hF₀'mem
    have hF₀'h : rightConjugate F₀' h ∈ conjSet E (sec2H F E) := by
      obtain ⟨θ, hθ, hθ'⟩ := hF₀'mem'
      exact ⟨θ * h, mul_mem hθ (mem_sup_right hh), by rw [hθ', rightConjugate_mul]⟩
    have hne : F₀' ≠ rightConjugate F₀' h := fun h' => by
      have hhN : h ∈ sec2P E ⊓ normalizer (F₀' : Set G) :=
        ⟨hh, (rightConjugate_eq_self_iff _ h).mp h'.symm⟩
      rw [sec2P_inf_normalizer_sec2F0_symm_eq h11 hE16 hF hL hodd hh hhS h4'] at hhN
      exact hhS (mem_sup_right hhN)
    have hsame := (inf_eq_sec2Z_and_card_inf h11 hE16 hF.symm hL hodd hh hhS' hx hxS' h4' h4
      hF₀'mem').1 _ hF₀'h hne
    have hle : F₀ ⊓ F₀' ≤ F₀' ⊓ rightConjugate F₀' h := fun f hf => by
      refine ⟨hf.2, (mem_rightConjugate_iff F₀' h f).mpr ?_⟩
      have h1 := (mem_centralizerMod.mp (hF₀M hf.1)).2.2 h⁻¹ (inv_mem hh)
      have hZF₀' : sec2Z A E F ≤ F₀' := by
        rw [hF.sec2Z_eq]
        have h2 : E ⊓ F ⊓ A ≤ F ⊓ A := fun z hz => ⟨hz.1.2, hz.2⟩
        exact h2.trans le_sup_left
      have h2 : h * f * h⁻¹ = f * (h⁻¹⁻¹ * f⁻¹ * h⁻¹ * f)⁻¹ := by group
      rw [h2]
      exact F₀'.mul_mem hf.2 (F₀'.inv_mem (hZF₀' h1))
    have h3 := card_le_of_le hle
    rw [hsame, hcross, sec2Z_comm, hF.card_sec2Z hodd] at h3
    omega
  have hM2 : (E ⊓ A).relIndex M ≠ 2 := by
    intro h2
    obtain ⟨f, hfM, hfEA⟩ : ∃ f ∈ M, f ∉ E ⊓ A := by
      by_contra hno
      push Not at hno
      have h1 : (E ⊓ A).relIndex M = 1 := relIndex_eq_one.mpr hno
      omega
    have hyf : y * f * y⁻¹ ∈ M := (mem_normalizer_iff.mp hyM f).mp hfM
    have hyfEA : y * f * y⁻¹ ∉ E ⊓ A := fun h' => hfEA (by
      have := (mem_normalizer_iff.mp (inv_mem hyEA) _).mp h'
      simpa [mul_assoc] using this)
    have hidx2 : ((E ⊓ A).subgroupOf M).index = 2 := h2
    have hmem := (mul_mem_iff_of_index_two hidx2 (a := (⟨f, hfM⟩ : ↥M)⁻¹)
      (b := ⟨y * f * y⁻¹, hyf⟩)).mpr (iff_of_false
        (fun h' => hfEA (mem_subgroupOf.mp (by simpa using (subgroupOf (E ⊓ A) M).inv_mem h')))
        (fun h' => hyfEA h'))
    have hfE := mem_of_conj_mem_of_torus h11 hE16 hF hL hodd hyA hyfix (hF₀C (hMF hfM))
      (mem_subgroupOf.mp hmem).1
    exact hfEA (by
      rw [← sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS]
      exact ⟨hMF hfM, hfE⟩)
  have h1 : (E ⊓ A).relIndex M = 1 := by
    have hpos : 0 < M.relIndex F₀ := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at hidx
      omega
    have hle : (E ⊓ A).relIndex M ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have : 3 * 2 ≤ (E ⊓ A).relIndex M * M.relIndex F₀ := Nat.mul_le_mul hgt (by omega)
      omega
    have hpos' : 0 < (E ⊓ A).relIndex M := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hidx
      omega
    omega
  exact le_antisymm (relIndex_eq_one.mp h1) hEAM

theorem centralizerMod_sec2P_sup_eq {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
    {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    centralizerMod (sec2P E ⊔ sec2S A R E F) (sec2P E ⊔ sec2S A R E F) (sec2Z A E F) =
      E ⊓ A := by
  set D := centralizerMod (sec2P E ⊔ sec2S A R E F) (sec2P E ⊔ sec2S A R E F) (sec2Z A E F)
    with hDdef
  set F₀ := sec2F0 A E x with hF₀
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  refine le_antisymm (fun d hd => ?_) (inf_le_centralizerMod_sec2P_sup h11 hE16 hF hL hodd)
  have hdC := centralizerMod_sec2P_sup_le h11 hE16 hF hL hodd hd
  have hEPS := sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS
  have hEF₀ : E ⊔ F₀ ≤ R ⊔ F₀ := by
    rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
    exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) le_sup_right
  have hRF₀ : R ≤ normalizer (F₀ : Set G) := hF.R_le_E.trans
    ((Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl).trans
      (sec2P_le_normalizer_sec2F0 h11 hE16 hF hL hodd hx hxS))
  have hd' : d ∈ ((R ⊔ F₀ : Subgroup G) : Set G) := by
    refine hEF₀ ?_
    rw [← hEPS, inf_comm, sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact hdC
  rw [coe_mul_of_left_le_normalizer_right R F₀ hRF₀] at hd'
  obtain ⟨r, hr, f₀, hf₀, rfl⟩ := hd'
  obtain ⟨y, hyA, hyE, hyF, hyEF, hyfix⟩ := exists_torus_sec2 hF hL hodd
  obtain ⟨hyZ, -, hyS⟩ := mem_normalizer_sec2S_of_mem hF hyA hyE hyF
  have hyP := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyPS : y ∈ normalizer ((sec2P E ⊔ sec2S A R E F : Subgroup G) : Set G) :=
    mem_normalizer_sup hyP hyS
  have hyD : y ∈ normalizer (D : Set G) := Sec2.mem_normalizer_centralizerMod hyPS hyPS hyZ
  have hyF₀ := mem_normalizer_sec2F0_of_mem h11 hE16 hF hL hodd hyA hyE hyF hx hxS
  have hyr : y * r * y⁻¹ = r := by
    rw [mem_centralizer_iff.mp (hRA hr) y hyA, mul_inv_cancel_right]
  have huD : (r * f₀)⁻¹ * (y * (r * f₀) * y⁻¹) ∈ D :=
    D.mul_mem (D.inv_mem hd) ((mem_normalizer_iff.mp hyD _).mp hd)
  have hu : (r * f₀)⁻¹ * (y * (r * f₀) * y⁻¹) = f₀⁻¹ * (y * f₀ * y⁻¹) := by
    calc (r * f₀)⁻¹ * (y * (r * f₀) * y⁻¹) = f₀⁻¹ * r⁻¹ * (y * r * y⁻¹) * (y * f₀ * y⁻¹) := by
          group
      _ = f₀⁻¹ * (y * f₀ * y⁻¹) := by rw [hyr]; group
  rw [hu] at huD
  have huF₀ : f₀⁻¹ * (y * f₀ * y⁻¹) ∈ F₀ :=
    F₀.mul_mem (F₀.inv_mem hf₀) ((mem_normalizer_iff.mp hyF₀ f₀).mp hf₀)
  have huM : f₀⁻¹ * (y * f₀ * y⁻¹) ∈ centralizerMod F₀ (sec2P E) (sec2Z A E F) := by
    obtain ⟨-, huZ, huc⟩ := mem_centralizerMod.mp huD
    exact mem_centralizerMod.mpr ⟨huF₀, huZ, fun p hp => huc p (mem_sup_left hp)⟩
  rw [centralizerMod_sec2F0_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'] at huM
  have hF₀C : F₀ ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd, inf_comm]
    exact sec2F0_le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS
  have hf₀E := mem_of_conj_mem_of_torus h11 hE16 hF hL hodd hyA hyfix (hF₀C hf₀) huM.1
  have hf₀EA : f₀ ∈ E ⊓ A := by
    rw [← sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS]
    exact ⟨hf₀, hf₀E⟩
  have hrD : r ∈ D := by
    have := D.mul_mem hd (D.inv_mem (inf_le_centralizerMod_sec2P_sup h11 hE16 hF hL hodd hf₀EA))
    simpa using this
  show r * f₀ ∈ E ⊓ A
  rw [eq_one_of_mem_R_of_mem_centralizerMod h11 hE16 hF hL hodd hr hrD, one_mul]
  exact hf₀EA

end Frame

theorem step25_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h22iv : Step22iv) : Step25 := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  have h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E)) := h22iv G A R g E F hS
  obtain ⟨h, hh, hhC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF hL hodd
  have hhS : h ∉ sec2S A R E F := fun hS' => hhC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact ⟨hS', hh⟩)
  obtain ⟨x, hx, hxC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  have hxS : x ∉ sec2S A R E F := fun hS' => hxC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF.symm hL hodd, hSc]
    exact ⟨hS', hx⟩)
  have hPSZ := sec2P_sup_sec2S_le_normalizer_sec2Z h11 hE16 hF hL hodd
  rw [← centralizerMod_sec2P_sup_eq h11 hE16 hF hL hodd hx hxS hh hhS h4 h4']
  ext d
  constructor
  · rintro ⟨hd, hdc⟩
    refine mem_centralizerMod.mpr ⟨hd, hPSZ hd, fun w hw => ?_⟩
    have h1 := (sec2Z A E F).inv_mem (hdc w hw)
    have h2 : (d⁻¹ * w⁻¹ * d * w)⁻¹ = w⁻¹ * d⁻¹ * w * d := by group
    rwa [h2] at h1
  · intro hd
    obtain ⟨hd, -, hdc⟩ := mem_centralizerMod.mp hd
    refine ⟨hd, fun w hw => ?_⟩
    have h1 := (sec2Z A E F).inv_mem (hdc w hw)
    have h2 : (w⁻¹ * d⁻¹ * w * d)⁻¹ = d⁻¹ * w⁻¹ * d * w := by group
    rwa [h2] at h1

end CFSG.ComponentClassification.AS81
