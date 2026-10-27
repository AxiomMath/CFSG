module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14A
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14B
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S17

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S14D

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem exists_R (hd : d.Hyp) :
    ∃ R : Subgroup G, R ≤ d.L ∧ IsElemAbelian 2 R ∧ Nat.card R = 32 ∧ d.pv 2 ∈ R ∧ R ≤ d.M ∧
      Nat.card (R ⊓ d.E : Subgroup G) ≤ 8 ∧
      ∃ c₀ ∈ centralizer ({d.t} : Set G), R = d.E.map (MulAut.conj c₀).toMonoidHom := by
  obtain ⟨c₄, hc₄D, hv2, hnorm, hcard⟩ := Model.exists_conj_hatE_parrottV_two
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hXD : Model.hatE.map (MulAut.conj c₄).toMonoidHom ≤ titsD := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Model.conj_mem_titsD_iff (titsD_le_titsA hc₄D) (titsD_le_titsA (hED hx))).2 (hED hx)
  obtain ⟨-, hE2, hEc, hE32⟩ := Model.card_hatE
  have hXc : ∀ a ∈ Model.hatE.map (MulAut.conj c₄).toMonoidHom,
      ∀ b ∈ Model.hatE.map (MulAut.conj c₄).toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c₄ * x * c₄⁻¹ * (c₄ * y * c₄⁻¹) = c₄ * (x * y) * c₄⁻¹ by group,
      show c₄ * y * c₄⁻¹ * (c₄ * x * c₄⁻¹) = c₄ * (y * x) * c₄⁻¹ by group, hEc x hx y hy]
  have hX2 : ∀ a ∈ Model.hatE.map (MulAut.conj c₄).toMonoidHom, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c₄ * x * c₄⁻¹ * (c₄ * x * c₄⁻¹) = c₄ * (x * x) * c₄⁻¹ by group, hE2 x hx]
    group
  have hX32 : Nat.card (Model.hatE.map (MulAut.conj c₄).toMonoidHom) = 32 := by
    rw [Model.card_map_conj, hE32]
  obtain ⟨hRcomm, hRsq⟩ := d.liftSub_elemAbelian hXc hX2
  have hc₀ : d.lift c₄ ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem c₄)
  refine ⟨d.liftSub (Model.hatE.map (MulAut.conj c₄).toMonoidHom), d.liftSub_le _,
    isElemAbelian_of_comm_sq hRcomm hRsq,
    by rw [d.card_liftSub hXD, hX32],
    Data.mem_liftSub.2 ⟨Model.parrottV 2, hv2, parrottV_two_mem_titsD, rfl⟩, ?_, ?_, d.lift c₄, hc₀, ?_⟩
  · intro r hr
    obtain ⟨x, hx, hxD, rfl⟩ := Data.mem_liftSub.1 hr
    exact lift_mem_M hd hxD (hnorm x hx)
  · have hEd : d.E = d.liftSub Model.hatE := rfl
    rw [hEd, ← liftSub_inf' hXD hED, d.card_liftSub (inf_le_left.trans hXD)]
    exact hcard
  · have hEd : d.E = d.liftSub Model.hatE := rfl
    rw [hEd, hd.map_conj_liftSub hc₀ hED, hd.ρ_lift hc₄D]

theorem six_seven_false (h49 : d.Thm49Statement) (hd : d.Hyp) (h11 : Node11 d z₀) (h13 : Node13 d)
    (hP1a : IsElemAbelian 2 (P1 d)) {k : G} (hkt : k * d.t * k⁻¹ = d.t * d.pv 2)
    (hDB : zpowers (d.t * d.pv 2) ⊔ (d.s56V ⊓ centralizer ({d.t * d.pv 2} : Set G)) =
      d.B.map (MulAut.conj k).toMonoidHom)
    (hVP : d.s56V = (P1 d).map (MulAut.conj k).toMonoidHom) : False := by
  obtain ⟨R, hRL, hRa, hR32, hv2R, hRM, hRE, c₀, hc₀, hRc₀⟩ := exists_R hd
  have hP1t := t_not_mem_P1 hd h13 hP1a
  have hU := inf_centralizer_eq_conj_F hd h11 hkt hP1t hDB hVP
  have ht2 := hd.t_mul_self
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb => elemAbelian_comm hRa ha hb
  have hRsq : ∀ a ∈ R, a * a = 1 := fun a ha => elemAbelian_sq hRa ha
  have hRt : ∀ r ∈ R, r * d.t = d.t * r := fun r hr => hd.L_comm_t (hRL hr)
  have hv2L : d.pv 2 ∈ d.L := pv_mem_L 2
  have hv2t : d.pv 2 * d.t = d.t * d.pv 2 := hd.L_comm_t hv2L
  have hRcs : ∀ r ∈ R, r * (d.t * d.pv 2) = (d.t * d.pv 2) * r := by
    intro r hr
    have h2 : r * d.pv 2 = d.pv 2 * r := hRcomm r hr _ hv2R
    calc r * (d.t * d.pv 2) = (r * d.t) * d.pv 2 := by group
      _ = d.t * (r * d.pv 2) := by rw [hRt r hr]; group
      _ = d.t * (d.pv 2 * r) := by rw [h2]
      _ = d.t * d.pv 2 * r := by group
  have hRN : R ≤ normalizer ((d.s56V ⊓ centralizer ({d.t * d.pv 2} : Set G) : Subgroup G) : Set G) := by
    intro r hr
    exact mem_normalizer_inf (M_le_Hg h49 hd (hRM hr)) (mem_normalizer_centralizer_singleton (hRcs r hr))
  have hR₁N := map_conj_inv_le_normalizer hRN hU
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Subgroup G, R₁ = R.map (MulAut.conj k⁻¹).toMonoidHom := ⟨_, rfl⟩
  rw [← hR₁] at hR₁N
  have hR₁mem : ∀ y, y ∈ R₁ ↔ k * y * k⁻¹ ∈ R := by
    intro y
    rw [hR₁, mem_map_conj_iff', inv_inv]
  have hR₁t : ∀ y ∈ R₁, y * d.t = d.t * y := by
    intro y hy
    have h1 := hRcs _ ((hR₁mem y).1 hy)
    rw [← hkt] at h1
    have h2 : k * (y * d.t) * k⁻¹ = k * (d.t * y) * k⁻¹ := by
      calc k * (y * d.t) * k⁻¹ = (k * y * k⁻¹) * (k * d.t * k⁻¹) := by group
        _ = (k * d.t * k⁻¹) * (k * y * k⁻¹) := h1
        _ = k * (d.t * y) * k⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hts : d.t ∉ R₁ := by
    intro ht
    have h1 := (hR₁mem d.t).1 ht
    rw [hkt] at h1
    apply hd.t_not_mem
    have e : d.t = (d.t * d.pv 2) * d.pv 2 := by rw [mul_assoc, pv2_mul_self, mul_one]
    rw [e]
    exact mul_mem (hRL h1) hv2L
  have hR₁a : IsElemAbelian 2 R₁ := by rw [hR₁]; exact isElemAbelian_map_conj hRa _
  have hR₁32 : Nat.card R₁ = 32 := by rw [hR₁, card_map_conj', hR32]
  have hR₁comm : ∀ a ∈ R₁, ∀ b ∈ R₁, a * b = b * a := fun a ha b hb => elemAbelian_comm hR₁a ha hb
  have hR₁sq : ∀ a ∈ R₁, a * a = 1 := fun a ha => elemAbelian_sq hR₁a ha
  obtain ⟨hA''comm, hA''sq⟩ := Data.sup_zpowers_elemAbelian ht2 hR₁t hR₁comm hR₁sq
  have hA''a : IsElemAbelian 2 (R₁ ⊔ zpowers d.t) := isElemAbelian_of_comm_sq hA''comm hA''sq
  have hA''C : R₁ ⊔ zpowers d.t ≤ centralizer ({d.t} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hR₁t y hy))
      (zpowers_le.2 d.t_mem_centralizer)
  have hts2 : Nat.card (zpowers d.t) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ht2) hd.t_ne_one]
  have hbot : R₁ ⊓ zpowers d.t = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    obtain ⟨haR, haT⟩ := ha
    rcases eq_one_or_of_mem_zpowers ht2 haT with h | h
    · rw [h]; exact one_mem _
    · exact absurd (h ▸ haR) hts
  have hzN : zpowers d.t ≤ normalizer (R₁ : Set G) := by
    rw [zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => hR₁t h hh)
  have hA''64 : Nat.card (R₁ ⊔ zpowers d.t : Subgroup G) = 2 ^ 6 := by
    rw [card_sup_of_inf_eq_bot' hzN hbot, hts2, hR₁32]
    norm_num
  have hs2 : (d.t * d.pv 2) * (d.t * d.pv 2) = 1 := by
    calc d.t * d.pv 2 * (d.t * d.pv 2) = d.t * (d.pv 2 * d.t) * d.pv 2 := by group
      _ = d.t * (d.t * d.pv 2) * d.pv 2 := by rw [hv2t]
      _ = (d.t * d.t) * (d.pv 2 * d.pv 2) := by group
      _ = 1 := by rw [ht2, pv2_mul_self]; group
  have hA'eq : R ⊔ zpowers d.t = R ⊔ zpowers (d.t * d.pv 2) := by
    have h1 : d.t * d.pv 2 ∈ R ⊔ zpowers d.t :=
      mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hv2R)
    have h2 : d.t ∈ R ⊔ zpowers (d.t * d.pv 2) := by
      have h3 : (d.t * d.pv 2) * d.pv 2 ∈ R ⊔ zpowers (d.t * d.pv 2) :=
        mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hv2R)
      rwa [mul_assoc, pv2_mul_self, mul_one] at h3
    exact le_antisymm (sup_le le_sup_left (zpowers_le.2 h2)) (sup_le le_sup_left (zpowers_le.2 h1))
  have hAc₀ : d.A.map (MulAut.conj c₀).toMonoidHom = R ⊔ zpowers d.t := by
    have hAdef : d.A = d.E ⊔ zpowers d.t := rfl
    rw [hAdef, Subgroup.map_sup, ← hRc₀, MonoidHom.map_zpowers]
    congr 2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_singleton_iff.1 hc₀]
    group
  have hA'' : R₁ ⊔ zpowers d.t = d.A.map (MulAut.conj (k⁻¹ * c₀)).toMonoidHom := by
    rw [← map_conj_map_conj', hAc₀, hA'eq, Subgroup.map_sup, ← hR₁, MonoidHom.map_zpowers]
    congr 2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hkt]
    group
  have hNA'' : Nat.card (normalizer ((R₁ ⊔ zpowers d.t : Subgroup G) : Set G)) = Nat.card d.M := by
    rw [hA'', card_normalizer_map_conj]
    rfl
  obtain ⟨c, hc, hcAB⟩ := hd.exists_map_conj_eq_A_or_B hA''C hA''a hA''64
  rcases hcAB with hA | hB
  ·
    have hA''c := eq_map_conj_inv_of_map_conj_eq hA
    have hc' : c⁻¹ ∈ centralizer ({d.t} : Set G) := inv_mem hc
    have hEL : d.E ≤ d.L := d.liftSub_le _
    have hFL : d.F ≤ d.L := d.liftSub_le _
    have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
    have hFD : Model.parrottF ≤ titsD := Model.parrottF_le_titsD
    have hE'A'' : d.E.map (MulAut.conj c⁻¹).toMonoidHom ≤ R₁ ⊔ zpowers d.t := by
      rw [hA''c]
      exact Subgroup.map_mono (le_sup_left : d.E ≤ d.E ⊔ zpowers d.t)
    have hE'L : d.E.map (MulAut.conj c⁻¹).toMonoidHom ≤ d.L := by
      rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hd.conj_mem ⟨c⁻¹, hc'⟩ (hEL he)
    have htN : d.t ∈ normalizer (d.F : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun f hf => hd.L_comm_t (hFL hf))
    have hE'N : ∀ y ∈ d.E.map (MulAut.conj c⁻¹).toMonoidHom, y ∈ normalizer (d.F : Set G) := by
      intro y hy
      have hy' := hE'A'' hy
      rcases (Data.mem_sup_zpowers_iff ht2 hR₁t).1 hy' with h | h
      · exact hR₁N h
      · have h2 := hR₁N h
        have e : y = d.t * (d.t * y) := by rw [← mul_assoc, ht2, one_mul]
        rw [e]
        exact mul_mem htN h2
    have haA := (d.ρ ⟨c⁻¹, hc'⟩).2
    have hE'lift : d.E.map (MulAut.conj c⁻¹).toMonoidHom = d.liftSub (Model.hatE.map
        (MulAut.conj (d.ρ ⟨c⁻¹, hc'⟩ : Equiv.Perm (Fin 1755))).toMonoidHom) :=
      hd.map_conj_liftSub hc' hED
    have hE'D : Model.hatE.map
        (MulAut.conj (d.ρ ⟨c⁻¹, hc'⟩ : Equiv.Perm (Fin 1755))).toMonoidHom ≤ titsD := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (Model.conj_mem_titsD_iff haA (titsD_le_titsA (hED hx))).2 (hED hx)
    have hNmodel : ∀ y ∈ Model.hatE.map
        (MulAut.conj (d.ρ ⟨c⁻¹, hc'⟩ : Equiv.Perm (Fin 1755))).toMonoidHom,
        y ∈ normalizer (Model.parrottF : Set (Equiv.Perm (Fin 1755))) := by
      intro y hy
      refine mem_normalizer_of_lift (d := d) hE'D hFD hy ?_
      have hly : d.lift y ∈ d.liftSub (Model.hatE.map
          (MulAut.conj (d.ρ ⟨c⁻¹, hc'⟩ : Equiv.Perm (Fin 1755))).toMonoidHom) :=
        Data.mem_liftSub.2 ⟨y, hy, hE'D hy, rfl⟩
      rw [← hE'lift] at hly
      exact hE'N _ hly
    have h16 := Model.sixteen_le_card_conj_hatE_inf_parrottF haA hNmodel
    have hcardE'F : 16 ≤ Nat.card (d.E.map (MulAut.conj c⁻¹).toMonoidHom ⊓ d.F : Subgroup G) := by
      have e1 : Nat.card (Model.hatE.map
          (MulAut.conj (d.ρ ⟨c⁻¹, hc'⟩ : Equiv.Perm (Fin 1755))).toMonoidHom ⊓ Model.parrottF :
          Subgroup (Equiv.Perm (Fin 1755))) =
          Nat.card (d.E.map (MulAut.conj c⁻¹).toMonoidHom ⊓ d.F : Subgroup G) := by
        rw [← d.card_liftSub (inf_le_left.trans hE'D), liftSub_inf' hE'D hFD, ← hE'lift]
        rfl
      omega
    have hPL : d.E.map (MulAut.conj c⁻¹).toMonoidHom ⊓ d.F ≤ d.L := inf_le_right.trans hFL
    have hPcard := (hd.tSup_facts hPL).2.2.2
    have htB : d.t ∈ d.B := mem_sup_right (mem_zpowers _)
    have htA'' : d.t ∈ R₁ ⊔ zpowers d.t := mem_sup_right (mem_zpowers _)
    have hPle : d.E.map (MulAut.conj c⁻¹).toMonoidHom ⊓ d.F ⊔ zpowers d.t ≤
        d.B ⊓ (R₁ ⊔ zpowers d.t) :=
      sup_le (le_inf (inf_le_right.trans (le_sup_left : d.F ≤ d.B)) (inf_le_left.trans hE'A''))
        (le_inf (zpowers_le.2 htB) (zpowers_le.2 htA''))
    have hlow := Subgroup.card_le_of_le hPle
    have hRB_t : ∀ p ∈ R₁ ⊓ d.B, p * d.t = d.t * p := fun p hp => hR₁t p hp.1
    have hBA''le : d.B ⊓ (R₁ ⊔ zpowers d.t) ≤ (R₁ ⊓ d.B) ⊔ zpowers d.t := by
      rintro x ⟨hxB, hxA⟩
      rw [Data.mem_sup_zpowers_iff ht2 hRB_t]
      rcases (Data.mem_sup_zpowers_iff ht2 hR₁t).1 hxA with h | h
      · exact Or.inl ⟨h, hxB⟩
      · exact Or.inr ⟨h, mul_mem htB hxB⟩
    have hbot' : (R₁ ⊓ d.B) ⊓ zpowers d.t = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      obtain ⟨haR, haT⟩ := ha
      rcases eq_one_or_of_mem_zpowers ht2 haT with h | h
      · rw [h]; exact one_mem _
      · exact absurd (h ▸ haR.1) hts
    have hzN' : zpowers d.t ≤ normalizer ((R₁ ⊓ d.B : Subgroup G) : Set G) := by
      rw [zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => hRB_t h hh)
    have hcard' : Nat.card ((R₁ ⊓ d.B) ⊔ zpowers d.t : Subgroup G) = Nat.card (R₁ ⊓ d.B : Subgroup G) * 2 := by
      rw [card_sup_of_inf_eq_bot' hzN' hbot', hts2]
    have hR₁B : R₁ ⊓ d.B = (R ⊓ d.B.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom := by
      rw [map_conj_inf, ← hR₁, map_conj_map_conj', inv_mul_cancel, map_conj_one']
    have hcardR₁B : Nat.card (R₁ ⊓ d.B : Subgroup G) =
        Nat.card (R ⊓ d.B.map (MulAut.conj k).toMonoidHom : Subgroup G) := by
      rw [hR₁B, card_map_conj']
    have hCMt : ∀ y, y ∈ d.s56V → y ∈ centralizer ({d.t} : Set G) → y ∈ d.E := by
      intro y hyV hyC
      rw [← CMt_inf_V h49 hd]
      exact ⟨mem_inf.2 ⟨V_le_M hyV, hyC⟩, hyV⟩
    have hst : (d.t * d.pv 2) * d.t = d.t * (d.t * d.pv 2) := by
      calc d.t * d.pv 2 * d.t = d.t * (d.pv 2 * d.t) := by group
        _ = d.t * (d.t * d.pv 2) := by rw [hv2t]
    have hRDE : R ⊓ d.B.map (MulAut.conj k).toMonoidHom ≤ R ⊓ d.E := by
      rintro x ⟨hxR, hxD⟩
      rw [← hDB, sup_comm] at hxD
      have hUs : ∀ p ∈ d.s56V ⊓ centralizer ({d.t * d.pv 2} : Set G),
          p * (d.t * d.pv 2) = (d.t * d.pv 2) * p := fun p hp =>
        mem_centralizer_singleton_iff.1 hp.2
      refine ⟨hxR, ?_⟩
      rcases (Data.mem_sup_zpowers_iff hs2 hUs).1 hxD with h | h
      · exact hCMt x h.1 (mem_centralizer_singleton_iff.2 (hRt x hxR))
      · exfalso
        have hxC : x * d.t = d.t * x := hRt x hxR
        have hu : (d.t * d.pv 2) * x ∈ d.E := by
          refine hCMt _ h.1 (mem_centralizer_singleton_iff.2 ?_)
          calc d.t * d.pv 2 * x * d.t = (d.t * d.pv 2) * (x * d.t) := by group
            _ = (d.t * d.pv 2) * (d.t * x) := by rw [hxC]
            _ = ((d.t * d.pv 2) * d.t) * x := by group
            _ = (d.t * (d.t * d.pv 2)) * x := by rw [hst]
            _ = d.t * (d.t * d.pv 2 * x) := by group
        apply hd.t_not_mem
        have hsL : d.t * d.pv 2 ∈ d.L := by
          have e : d.t * d.pv 2 = ((d.t * d.pv 2) * x) * x⁻¹ := by group
          rw [e]
          exact mul_mem (hEL hu) (inv_mem (hRL hxR))
        have e2 : d.t = (d.t * d.pv 2) * (d.pv 2)⁻¹ := by group
        rw [e2]
        exact mul_mem hsL (inv_mem hv2L)
    have hle8 : Nat.card (R₁ ⊓ d.B : Subgroup G) ≤ 8 := by
      rw [hcardR₁B]
      exact (Subgroup.card_le_of_le hRDE).trans hRE
    have hup := Subgroup.card_le_of_le hBA''le
    omega
  ·
    have h1 := eq_map_conj_inv_of_map_conj_eq hB
    have hNB : Nat.card (normalizer ((R₁ ⊔ zpowers d.t : Subgroup G) : Set G)) = Nat.card d.N := by
      rw [h1, card_normalizer_map_conj]
      rfl
    rw [hNA''] at hNB
    rcases hd.card_M_N_values h49 with ⟨-, hM, hN⟩ | ⟨-, hM, hN⟩ <;>
      · rw [hM, hN] at hNB
        omega

end S14D

end CFSG.LocalAnalysis.EvenBN.Tits.N
