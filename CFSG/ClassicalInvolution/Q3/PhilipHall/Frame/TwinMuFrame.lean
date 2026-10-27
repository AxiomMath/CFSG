module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T

section Alg

variable {G : Type} [Group G]

theorem conj_of_comm {r a b : G} (h : r * a = a * r) :
    r * (a * b) * r⁻¹ = a * (r * b * r⁻¹) := by
  have e : r * a * r⁻¹ = a := by rw [h]; group
  calc r * (a * b) * r⁻¹ = (r * a * r⁻¹) * (r * b * r⁻¹) := by group
    _ = a * (r * b * r⁻¹) := by rw [e]

theorem rev4 {x₀ x₁ x₂ x₃ : G} (c01 : x₀ * x₁ = x₁ * x₀) (c02 : x₀ * x₂ = x₂ * x₀)
    (c03 : x₀ * x₃ = x₃ * x₀) (c12 : x₁ * x₂ = x₂ * x₁) (c13 : x₁ * x₃ = x₃ * x₁)
    (c23 : x₂ * x₃ = x₃ * x₂) : x₃ * x₂ * x₁ * x₀ = x₀ * x₁ * x₂ * x₃ := by
  have rev3 : x₃ * x₂ * x₁ = x₁ * x₂ * x₃ := by
    calc x₃ * x₂ * x₁ = x₃ * (x₂ * x₁) := mul_assoc _ _ _
      _ = x₃ * (x₁ * x₂) := by rw [c12]
      _ = x₃ * x₁ * x₂ := (mul_assoc _ _ _).symm
      _ = x₁ * x₃ * x₂ := by rw [c13]
      _ = x₁ * (x₃ * x₂) := mul_assoc _ _ _
      _ = x₁ * (x₂ * x₃) := by rw [c23]
      _ = x₁ * x₂ * x₃ := (mul_assoc _ _ _).symm
  have h0 : x₀ * (x₁ * x₂ * x₃) = (x₁ * x₂ * x₃) * x₀ := by
    have : Commute x₀ (x₁ * x₂ * x₃) :=
      ((show Commute x₀ x₁ from c01).mul_right (show Commute x₀ x₂ from c02)).mul_right
        (show Commute x₀ x₃ from c03)
    exact this.eq
  calc x₃ * x₂ * x₁ * x₀ = (x₁ * x₂ * x₃) * x₀ := by rw [rev3]
    _ = x₀ * (x₁ * x₂ * x₃) := h0.symm
    _ = x₀ * x₁ * x₂ * x₃ := by simp only [mul_assoc]

theorem braid_contra {A B c w z : G} (hAw : A * w * A⁻¹ = c * w) (hAc : A * c * A⁻¹ = c⁻¹)
    (hBw : B * w * B⁻¹ = w⁻¹) (hBc : B * c * B⁻¹ = w⁻¹ * c) (hcw : c * w = w * c)
    (hcc : c * c = z) (hzz : z * z = 1)
    (hP : (A * B * A) * c * (A * B * A)⁻¹ = (B * A * B) * c * (B * A * B)⁻¹) : w * w = 1 := by
  have hBci : B * c⁻¹ * B⁻¹ = c⁻¹ * w := by
    rw [show B * c⁻¹ * B⁻¹ = (B * c * B⁻¹)⁻¹ by group, hBc]; group
  have hAci : A * c⁻¹ * A⁻¹ = c := by
    rw [show A * c⁻¹ * A⁻¹ = (A * c * A⁻¹)⁻¹ by group, hAc, inv_inv]
  have l1 : (A * B * A) * c * (A * B * A)⁻¹ = c * (c * w) := by
    calc (A * B * A) * c * (A * B * A)⁻¹ = A * (B * (A * c * A⁻¹) * B⁻¹) * A⁻¹ := by group
      _ = A * (B * c⁻¹ * B⁻¹) * A⁻¹ := by rw [hAc]
      _ = A * (c⁻¹ * w) * A⁻¹ := by rw [hBci]
      _ = (A * c⁻¹ * A⁻¹) * (A * w * A⁻¹) := by group
      _ = c * (c * w) := by rw [hAci, hAw]
  have r1 : (B * A * B) * c * (B * A * B)⁻¹ = w * c⁻¹ * w * (c⁻¹ * w) := by
    calc (B * A * B) * c * (B * A * B)⁻¹ = B * (A * (B * c * B⁻¹) * A⁻¹) * B⁻¹ := by group
      _ = B * (A * (w⁻¹ * c) * A⁻¹) * B⁻¹ := by rw [hBc]
      _ = B * ((A * w * A⁻¹)⁻¹ * (A * c * A⁻¹)) * B⁻¹ := by group
      _ = B * ((c * w)⁻¹ * c⁻¹) * B⁻¹ := by rw [hAw, hAc]
      _ = ((B * c * B⁻¹) * (B * w * B⁻¹))⁻¹ * (B * c * B⁻¹)⁻¹ := by group
      _ = ((w⁻¹ * c) * w⁻¹)⁻¹ * (w⁻¹ * c)⁻¹ := by rw [hBc, hBw]
      _ = w * c⁻¹ * w * (c⁻¹ * w) := by group
  have hE : c * (c * w) = w * c⁻¹ * w * (c⁻¹ * w) := l1.symm.trans (hP.trans r1)
  have hcwi : c⁻¹ * w = w * c⁻¹ := (Commute.inv_left (show Commute c w from hcw)).eq
  have hzw : z * w = w * z := by
    rw [← hcc]
    exact ((show Commute c w from hcw).mul_left (show Commute c w from hcw)).eq
  have e1 : c * (c * w) = z * w := by rw [← hcc, mul_assoc]
  have e2 : w * c⁻¹ * w * (c⁻¹ * w) = w * w * w * (c⁻¹ * c⁻¹) := by
    calc w * c⁻¹ * w * (c⁻¹ * w) = w * (c⁻¹ * w) * (c⁻¹ * w) := by simp only [mul_assoc]
      _ = w * (w * c⁻¹) * (w * c⁻¹) := by rw [hcwi]
      _ = w * w * (c⁻¹ * w) * c⁻¹ := by simp only [mul_assoc]
      _ = w * w * (w * c⁻¹) * c⁻¹ := by rw [hcwi]
      _ = w * w * w * (c⁻¹ * c⁻¹) := by simp only [mul_assoc]
  have e3 : c⁻¹ * c⁻¹ = z := by
    have : c⁻¹ * c⁻¹ = (c * c)⁻¹ := by group
    rw [this, hcc]
    exact inv_eq_of_mul_eq_one_left hzz
  have hE' : z * w = w * w * w * z := by rw [← e1, hE, e2, e3]
  have h5 : w * z = w * w * w * z := hzw.symm.trans hE'
  have h6 : w = w * w * w := mul_right_cancel h5
  have h7 : w * 1 = w * (w * w) := by
    rw [mul_one]
    calc w = w * w * w := h6
      _ = w * (w * w) := mul_assoc _ _ _
  exact (mul_left_cancel h7).symm

end Alg

section Cyc

variable {G : Type} [Group G] [Finite G]

theorem cyc_inv {U : Subgroup G} (hU : IsCyclic ↥U) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (haa : a * a = 1) (hbb : b * b = 1) (hb1 : b ≠ 1) : a = 1 ∨ a = b := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, hab'⟩ := hcon
  have : Fintype ↥U := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥U) (n := 2) (by norm_num)
  let A : ↥U := ⟨a, ha⟩
  let B : ↥U := ⟨b, hb⟩
  have hA1 : A ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hB1 : B ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hAB : A ≠ B := fun h => hab' (congrArg Subtype.val h)
  have h3 : ({1, A, B} : Finset ↥U) ⊆ Finset.univ.filter (fun x : ↥U => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · apply Subtype.ext
      simpa [sq] using haa
    · apply Subtype.ext
      simpa [sq] using hbb
  have hcard : ({1, A, B} : Finset ↥U).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hAB]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hA1 h.symm, fun h => hB1 h.symm⟩
  have := Finset.card_le_card h3
  omega

theorem eq_or_inv {U : Subgroup G} (hU : IsCyclic ↥U) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a * b = b * a) (h : a * a = b * b) (hbb : (b * b) * (b * b) = 1) (hb2 : b * b ≠ 1) :
    a = b ∨ a = b⁻¹ := by
  have hx : a * b⁻¹ ∈ U := U.mul_mem ha (U.inv_mem hb)
  have hbi : a * b⁻¹ = b⁻¹ * a := (Commute.inv_right (show Commute a b from hab)).eq
  have hxx : (a * b⁻¹) * (a * b⁻¹) = 1 := by
    calc (a * b⁻¹) * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ := by simp only [mul_assoc]
      _ = a * (a * b⁻¹) * b⁻¹ := by rw [← hbi]
      _ = (a * a) * (b⁻¹ * b⁻¹) := by simp only [mul_assoc]
      _ = (b * b) * (b * b)⁻¹ := by rw [h]; group
      _ = 1 := mul_inv_cancel _
  have hι : b * b ∈ U := U.mul_mem hb hb
  rcases cyc_inv hU hx hι hxx hbb hb2 with h1 | h1
  · left
    exact mul_inv_eq_one.mp h1
  · right
    have h2 : a = b * b * b := by
      calc a = (a * b⁻¹) * b := by group
        _ = b * b * b := by rw [h1]
    rw [h2]
    refine eq_inv_of_mul_eq_one_left ?_
    calc b * b * b * b = (b * b) * (b * b) := by simp only [mul_assoc]
      _ = 1 := hbb

end Cyc

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

structure Frame4 (Ω : Set (Subgroup G)) (W : Subgroup G) (a b c d : Rep Ω W) : Prop where
  ab : b.K ∈ omegaNbr Ω a.K
  ba : a.K ∈ omegaNbr Ω b.K
  ac : c.K ∈ omegaNbr Ω a.K
  ca : a.K ∈ omegaNbr Ω c.K
  ad : d.K ∈ omegaNbr Ω a.K
  da : a.K ∈ omegaNbr Ω d.K
  bc : c.K ∈ omegaNbr Ω b.K
  cb : b.K ∈ omegaNbr Ω c.K
  bd : d.K ∈ omegaNbr Ω b.K
  db : b.K ∈ omegaNbr Ω d.K
  cd : d.K ∈ omegaNbr Ω c.K
  dc : c.K ∈ omegaNbr Ω d.K

theorem nbr_of_comm (ctx : Q3CL.Thompson.Ctx Ω W) {α β : Rep Ω W}
    (hne : MuTab.muTabElt α ≠ MuTab.muTabElt β)
    (hc : MuTab.muTabElt α * MuTab.muTabElt β = MuTab.muTabElt β * MuTab.muTabElt α) :
    β.K ∈ omegaNbr Ω α.K := by
  have hK : α.K ≠ β.K := fun h => hne (Subtype.ext (Q3T6.Mu.ctx_img_eq_of_K_eq ctx α β h))
  refine Q3T6.Mu.ctx_omega_of_comm ctx α β hK ?_
  have h' : (↑(MuTab.muTabElt α) * ↑(MuTab.muTabElt β) : NQuot (W ⊔ OCW W)) =
      ↑(MuTab.muTabElt β) * ↑(MuTab.muTabElt α) := congrArg Subtype.val hc
  exact h'

theorem not_adj_of_noncomm (ctx : Q3CL.Thompson.Ctx Ω W) {α β : Rep Ω W}
    (h : MuTab.muTabElt α * MuTab.muTabElt β ≠ MuTab.muTabElt β * MuTab.muTabElt α) :
    β.K ≠ α.K ∧ β.K ∉ omegaNbr Ω α.K := by
  constructor
  · intro hK
    apply h
    have h1 := Q3T6.Mu.ctx_img_eq_of_K_eq ctx β α hK
    have h2 : MuTab.muTabElt β = MuTab.muTabElt α := Subtype.ext h1
    rw [h2]
  · intro hn
    apply h
    have h1 := Q3T6.Mu.ctx_comm_of_omega ctx α β hn
    exact Subtype.ext h1

theorem Frame4.of_comm (ctx : Q3CL.Thompson.Ctx Ω W) {a b c d : Rep Ω W}
    (hab : MuTab.muTabElt a ≠ MuTab.muTabElt b) (hac : MuTab.muTabElt a ≠ MuTab.muTabElt c)
    (had : MuTab.muTabElt a ≠ MuTab.muTabElt d) (hbc : MuTab.muTabElt b ≠ MuTab.muTabElt c)
    (hbd : MuTab.muTabElt b ≠ MuTab.muTabElt d) (hcd : MuTab.muTabElt c ≠ MuTab.muTabElt d)
    (cab : MuTab.muTabElt a * MuTab.muTabElt b = MuTab.muTabElt b * MuTab.muTabElt a)
    (cac : MuTab.muTabElt a * MuTab.muTabElt c = MuTab.muTabElt c * MuTab.muTabElt a)
    (cad : MuTab.muTabElt a * MuTab.muTabElt d = MuTab.muTabElt d * MuTab.muTabElt a)
    (cbc : MuTab.muTabElt b * MuTab.muTabElt c = MuTab.muTabElt c * MuTab.muTabElt b)
    (cbd : MuTab.muTabElt b * MuTab.muTabElt d = MuTab.muTabElt d * MuTab.muTabElt b)
    (ccd : MuTab.muTabElt c * MuTab.muTabElt d = MuTab.muTabElt d * MuTab.muTabElt c) :
    Frame4 Ω W a b c d :=
  ⟨nbr_of_comm ctx hab cab, nbr_of_comm ctx hab.symm cab.symm, nbr_of_comm ctx hac cac,
    nbr_of_comm ctx hac.symm cac.symm, nbr_of_comm ctx had cad, nbr_of_comm ctx had.symm cad.symm,
    nbr_of_comm ctx hbc cbc, nbr_of_comm ctx hbc.symm cbc.symm, nbr_of_comm ctx hbd cbd,
    nbr_of_comm ctx hbd.symm cbd.symm, nbr_of_comm ctx hcd ccd, nbr_of_comm ctx hcd.symm ccd.symm⟩

theorem piG_mul4 {a b c d : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) (hc : c ∈ Subgroup.normalizer (W : Set G))
    (hd : d ∈ Subgroup.normalizer (W : Set G)) :
    piG W (a * b * c * d) = piG W a * piG W b * piG W c * piG W d := by
  rw [piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) hc) hd,
    piG_mul (Subgroup.mul_mem _ ha hb) hc, piG_mul ha hb]

theorem frame_prod_gen (ctx : Q3CL.Thompson.Ctx Ω W) {ρa ρb ρc ρd σa σb σc σd : Rep Ω W}
    (hF : Frame4 Ω W ρa ρb ρc ρd) (hF' : Frame4 Ω W σa σb σc σd)
    (hcen : piG W (ρd.r * ρc.r * ρb.r * ρa.r) = piG W (σd.r * σc.r * σb.r * σa.r))
    (nea : σa.K ≠ ρa.K) (neb : σa.K ≠ ρb.K) (nec : σa.K ≠ ρc.K) (ned : σa.K ≠ ρd.K)
    (nta : σa.K ∉ omegaNbr Ω ρa.K) (ntb : σa.K ∉ omegaNbr Ω ρb.K)
    (ntc : σa.K ∉ omegaNbr Ω ρc.K) (ntd : σa.K ∉ omegaNbr Ω ρd.K)
    {w zS za zb zc zd : G} (hw : w ∈ σa.K ⊓ W) (hzS : IsUniqueInvolution σa.K zS)
    (hw2 : w * w = zS) (hza : IsUniqueInvolution ρa.K za) (hzb : IsUniqueInvolution ρb.K zb)
    (hzc : IsUniqueInvolution ρc.K zc) (hzd : IsUniqueInvolution ρd.K zd) :
    ∃ ka kb kc kd : G, ka ∈ ρa.K ⊓ W ∧ kb ∈ ρb.K ⊓ W ∧ kc ∈ ρc.K ⊓ W ∧ kd ∈ ρd.K ⊓ W ∧
      ka * ka = za ∧ kb * kb = zb ∧ kc * kc = zc ∧ kd * kd = zd ∧
      ρa.r * w * ρa.r⁻¹ = ka * w ∧ ρb.r * w * ρb.r⁻¹ = kb * w ∧ ρc.r * w * ρc.r⁻¹ = kc * w ∧
      ρd.r * w * ρd.r⁻¹ = kd * w ∧ ka * kb * kc * kd = zS := by
  have hΩ := ctx.hΩ
  have hcW := ctx.comm_W
  obtain ⟨ka, hka⟩ : ∃ ka, ka = ρa.r * w * ρa.r⁻¹ * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, kb = ρb.r * w * ρb.r⁻¹ * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ kc, kc = ρc.r * w * ρc.r⁻¹ * w⁻¹ := ⟨_, rfl⟩
  obtain ⟨kd, hkd⟩ : ∃ kd, kd = ρd.r * w * ρd.r⁻¹ * w⁻¹ := ⟨_, rfl⟩
  have ma : ka ∈ ρa.K ⊓ W := hka ▸ ctx.comm_mem ρa σa nea.symm hw
  have mb : kb ∈ ρb.K ⊓ W := hkb ▸ ctx.comm_mem ρb σa neb.symm hw
  have mc : kc ∈ ρc.K ⊓ W := hkc ▸ ctx.comm_mem ρc σa nec.symm hw
  have md : kd ∈ ρd.K ⊓ W := hkd ▸ ctx.comm_mem ρd σa ned.symm hw
  have sa : ka * ka = za := by
    rw [hka]; exact ctx.comm_sq ρa σa nea.symm nta hw hza hzS hw2
  have sb : kb * kb = zb := by
    rw [hkb]; exact ctx.comm_sq ρb σa neb.symm ntb hw hzb hzS hw2
  have sc : kc * kc = zc := by
    rw [hkc]; exact ctx.comm_sq ρc σa nec.symm ntc hw hzc hzS hw2
  have sd : kd * kd = zd := by
    rw [hkd]; exact ctx.comm_sq ρd σa ned.symm ntd hw hzd hzS hw2
  have ra : ρa.r * w * ρa.r⁻¹ = ka * w := by rw [hka]; group
  have rb : ρb.r * w * ρb.r⁻¹ = kb * w := by rw [hkb]; group
  have rc : ρc.r * w * ρc.r⁻¹ = kc * w := by rw [hkc]; group
  have rd : ρd.r * w * ρd.r⁻¹ = kd * w := by rw [hkd]; group
  have kab : ρb.r * ka = ka * ρb.r := ctx.centralizes ρb ρa hF.ba ma
  have kac : ρc.r * ka = ka * ρc.r := ctx.centralizes ρc ρa hF.ca ma
  have kad : ρd.r * ka = ka * ρd.r := ctx.centralizes ρd ρa hF.da ma
  have kbc : ρc.r * kb = kb * ρc.r := ctx.centralizes ρc ρb hF.cb mb
  have kbd : ρd.r * kb = kb * ρd.r := ctx.centralizes ρd ρb hF.db mb
  have kcd : ρd.r * kc = kc * ρd.r := ctx.centralizes ρd ρc hF.dc mc
  have s1 : ρb.r * (ka * w) * ρb.r⁻¹ = ka * (kb * w) := by
    rw [conj_of_comm kab, rb]
  have s2 : ρc.r * (ka * (kb * w)) * ρc.r⁻¹ = ka * (kb * (kc * w)) := by
    rw [conj_of_comm kac, conj_of_comm kbc, rc]
  have s3 : ρd.r * (ka * (kb * (kc * w))) * ρd.r⁻¹ = ka * (kb * (kc * (kd * w))) := by
    rw [conj_of_comm kad, conj_of_comm kbd, conj_of_comm kcd, rd]
  have hRw : (ρd.r * ρc.r * ρb.r * ρa.r) * w * (ρd.r * ρc.r * ρb.r * ρa.r)⁻¹ =
      ka * (kb * (kc * (kd * w))) := by
    calc (ρd.r * ρc.r * ρb.r * ρa.r) * w * (ρd.r * ρc.r * ρb.r * ρa.r)⁻¹
        = ρd.r * (ρc.r * (ρb.r * (ρa.r * w * ρa.r⁻¹) * ρb.r⁻¹) * ρc.r⁻¹) * ρd.r⁻¹ := by group
      _ = ka * (kb * (kc * (kd * w))) := by rw [ra, s1, s2, s3]
  have hsb : σb.r * w = w * σb.r := ctx.centralizes σb σa hF'.ba hw
  have hsc : σc.r * w = w * σc.r := ctx.centralizes σc σa hF'.ca hw
  have hsd : σd.r * w = w * σd.r := ctx.centralizes σd σa hF'.da hw
  have hs0 : σa.r * w * σa.r⁻¹ = w⁻¹ := ctx.conj_inv σa hw
  have hmw : Commute (σd.r * σc.r * σb.r) w :=
    (((show Commute σd.r w from hsd).mul_left (show Commute σc.r w from hsc)).mul_left
      (show Commute σb.r w from hsb))
  have hSw : (σd.r * σc.r * σb.r * σa.r) * w * (σd.r * σc.r * σb.r * σa.r)⁻¹ = w⁻¹ := by
    calc (σd.r * σc.r * σb.r * σa.r) * w * (σd.r * σc.r * σb.r * σa.r)⁻¹
        = (σd.r * σc.r * σb.r) * (σa.r * w * σa.r⁻¹) * (σd.r * σc.r * σb.r)⁻¹ := by group
      _ = (σd.r * σc.r * σb.r) * w⁻¹ * (σd.r * σc.r * σb.r)⁻¹ := by rw [hs0]
      _ = w⁻¹ := by
        have : Commute (σd.r * σc.r * σb.r) w⁻¹ := hmw.inv_right
        rw [this.eq]; group
  have hRN : (ρd.r * ρc.r * ρb.r * ρa.r) ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ρd.r_mem_normalizer
      ρc.r_mem_normalizer) ρb.r_mem_normalizer) ρa.r_mem_normalizer
  have hSN : (σd.r * σc.r * σb.r * σa.r) ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ σd.r_mem_normalizer
      σc.r_mem_normalizer) σb.r_mem_normalizer) σa.r_mem_normalizer
  have hconj := Q3CL.Thompson.conj_eq_of_piG_eq hΩ ctx.hW hRN hSN hcen hw.2
  rw [hSw, hRw] at hconj
  have hP : (ka * kb * kc * kd) * w = w⁻¹ := by
    rw [hconj]; simp only [mul_assoc]
  have hprod : ka * kb * kc * kd = w⁻¹ * w⁻¹ := by
    calc ka * kb * kc * kd = ((ka * kb * kc * kd) * w) * w⁻¹ := by group
      _ = w⁻¹ * w⁻¹ := by rw [hP]
  have hzS' : w⁻¹ * w⁻¹ = zS := by
    rw [← mul_inv_rev, hw2]
    exact inv_eq_of_mul_eq_one_left hzS.sq
  exact ⟨ka, kb, kc, kd, ma, mb, mc, md, sa, sb, sc, sd, ra, rb, rc, rd, hprod.trans hzS'⟩

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
