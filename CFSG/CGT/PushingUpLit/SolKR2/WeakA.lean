module

public import CFSG.CGT.PushingUpLit.SolKR2.WeakDefs
public import CFSG.CGT.PushingUpLit.SolKR2.Pair
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup IsTI BenderCenterInput
  UnitaryTwoGenerationInput)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G] [Finite G] {M B : Subgroup G}

namespace R2

variable (h : R2 M B)
include h

omit [Finite G] in
theorem conj_U_ne_bot (e : G) : conjSubgroup e (omegaTwoSub B) ≠ ⊥ := by
  intro hbot
  have := Pair.card_conj_U h e
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem centralizer_U_le : Subgroup.centralizer (omegaTwoSub B : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans h.normalizer_U.le

theorem conj_cent_le {m e : G} (hm : m ∈ M)
    (he : conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    conjSubgroup (m * e) (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) := by
  intro z hz
  rw [conjSubgroup_mul] at hz
  have hz' : m⁻¹ * z * m ∈ conjSubgroup e (omegaTwoSub B) := mem_conjSubgroup.mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : m⁻¹ * u * m ∈ omegaTwoSub B := by
    have := (Subgroup.mem_normalizer_iff.mp (h.normalizer_U.ge (M.inv_mem hm)) u).mp hu
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp (he hz') _ hu'
  calc u * z = m * ((m⁻¹ * u * m) * (m⁻¹ * z * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * z * m) * (m⁻¹ * u * m)) * m⁻¹ := by rw [h1]
    _ = z * u := by group

theorem comm_of_cent_elem {f c a : G} (ha : a ∈ conjSubgroup f (omegaOneSub B)) (ha1 : a ≠ 1)
    (hC : ∀ u ∈ conjSubgroup c (omegaTwoSub B), u * a = a * u) :
    ∀ x ∈ conjSubgroup c (omegaTwoSub B), ∀ y ∈ conjSubgroup f (omegaTwoSub B),
      x * y = y * x := by
  have hle : conjSubgroup (c * f⁻¹) (conjSubgroup f (omegaTwoSub B)) ≤
      Subgroup.normalizer (conjSubgroup f (omegaTwoSub B) : Set G) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
    exact fun u hu => Pair.mem_normalizer_conj_U h ha ha1 (hC u hu)
  have hc := commute_of_le_normalizer (Pair.comm_conj_U h f)
    ((Pair.isPGroup_U h).map (MulAut.conj f).toMonoidHom) (h.conj_U_ne_bot f)
    (isTI_conjSubgroup h.s3hyp.ti f) hle
  rw [← conjSubgroup_mul, inv_mul_cancel_right] at hc
  intro x hx y hy
  exact (hc y hy x hx).symm

theorem delta_of_ne_one {e a : G} (ha : a ∈ conjSubgroup e (omegaOneSub B)) (ha1 : a ≠ 1)
    (hC : a ∈ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) := by
  have hcomm := h.comm_of_cent_elem (f := e) (c := 1) ha ha1 (fun u hu => by
    rw [conjSubgroup_one] at hu
    exact Subgroup.mem_centralizer_iff.mp hC u hu)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hcomm u (by rwa [conjSubgroup_one]) x hx

theorem delta_of_gamma {e : G}
    (he : conjSubgroup e (omegaOneSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Pair.conj_B0_ne_bot h e)
  exact h.delta_of_ne_one ha (fun e' => ha1 (Subtype.ext e')) (he ha)

theorem comm_of_cent {f c : G}
    (hf : conjSubgroup f (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup c (omegaTwoSub B) : Set G)) :
    ∀ a ∈ conjSubgroup c (omegaTwoSub B), ∀ b ∈ conjSubgroup f (omegaTwoSub B),
      a * b = b * a := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Pair.conj_B0_ne_bot h f)
  exact h.comm_of_cent_elem ha (fun e' => ha1 (Subtype.ext e')) (fun u hu =>
    Subgroup.mem_centralizer_iff.mp (hf ha) u hu)

end R2

section Certificates34

namespace R2

variable (h : R2 M B)
include h

theorem mem_of_comm {g : G}
    (hcomm : ∀ A ∈ Lam M B, ∀ a ∈ A, ∀ c ∈ conjSubgroup g (omegaOneSub B), a * c = c * a) :
    g ∈ M := by
  have hV := h.omegaOne_omegaTwo
  refine h.s3hyp.mem_of_comm (g := g) (fun k hk a ha c hc => ?_) (fun k hk a ha c hc => ?_)
  · rw [hV] at hk ha hc
    exact hcomm _ ⟨k, rfl, hk⟩ a ha c hc
  · rw [hV] at hk ha hc
    exact R2.comm_B0 h ⟨k, rfl, hk⟩ a ha c hc

end R2

theorem r2Weak_of_star (hS : R2Star) : R2Weak := by
  intro G _ _ M B h g hg
  have hmem : g ∈ M := h.mem_of_comm (fun A hA a ha c hc => hS G M B h g hg A hA a ha c hc)
  exact conjSubgroup_eq_self_iff.mpr (h.s3hyp.normal hmem)

namespace R2

variable (h : R2 M B)
include h

theorem gamma_le_Q {e : G}
    (he : conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    conjSubgroup e (omegaOneSub B) ≤ inSubgroup (pCore 2) M := by
  have H := h.s3hyp
  have heM : conjSubgroup e (omegaTwoSub B) ≤ M := he.trans h.centralizer_U_le
  rcases tim78_2_15 CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
    H.fstar heM (Pair.comm_conj_U h e) ((Pair.isPGroup_U h).map (MulAut.conj e).toMonoidHom)
    (fun k _ => isTI_conjSubgroup H.ti e k) with h1 | h2 | ⟨hQ, -⟩
  · exact absurd h1 (H.omega_conj_ne e)
  · exact absurd h2 (H.not_isCyclic_conj e)
  · rwa [Pair.omegaOne_conj_U h e] at hQ

theorem gamma_comm_abs {e e' : G}
    (he : conjSubgroup e (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G))
    (he' : conjSubgroup e' (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G)) :
    ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
      a * b = b * a := by
  have H := h.s3hyp
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have heM : conjSubgroup e (omegaTwoSub B) ≤ M := he.trans h.centralizer_U_le
  have hE2 : IsPGroup 2 (conjSubgroup e (omegaTwoSub B)) :=
    (Pair.isPGroup_U h).map (MulAut.conj e).toMonoidHom
  have hS : IsPGroup 2 ↥(conjSubgroup e (omegaTwoSub B) ⊔ inSubgroup (pCore 2) M) :=
    IsPGroup.to_sup_of_normal_right' hE2 hQ2 (heM.trans hMQ)
  have hconj : conjSubgroup (e' * e⁻¹) (conjSubgroup e (omegaTwoSub B)) =
      conjSubgroup e' (omegaTwoSub B) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have h4 : 4 ≤ Nat.card ↥(omegaOneSub (conjSubgroup (e' * e⁻¹)
      (conjSubgroup e (omegaTwoSub B))) ⊓
        (conjSubgroup e (omegaTwoSub B) ⊔ inSubgroup (pCore 2) M)) := by
    rw [hconj, Pair.omegaOne_conj_U h e', inf_of_le_left ((h.gamma_le_Q he').trans le_sup_right),
      Pair.card_conj_B0 h e']
  have key := tim78_2_14_b CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput (Pair.comm_conj_U h e) hE2
    (isTI_conjSubgroup H.ti e) (H.omega_conj_ne e) hS le_sup_left (e' * e⁻¹) h4
  rw [hconj, Pair.omegaOne_conj_U h e', Pair.omegaOne_conj_U h e] at key
  exact key

theorem gamma_comm (f e e' : G)
    (he : conjSubgroup e (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G))
    (he' : conjSubgroup e' (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G)) :
    ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
      a * b = b * a := by
  have key : ∀ e₀ : G, conjSubgroup e₀ (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
      conjSubgroup (f⁻¹ * e₀) (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G) := by
    intro e₀ he₀
    refine h.delta_of_gamma (fun z hz => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hz' : f * z * f⁻¹ ∈ conjSubgroup e₀ (omegaOneSub B) := by
      rw [conjSubgroup_mul, mem_conjSubgroup, inv_inv] at hz
      exact hz
    have hfu : f * u * f⁻¹ ∈ conjSubgroup f (omegaTwoSub B) := by
      rw [mem_conjSubgroup, show f⁻¹ * (f * u * f⁻¹) * f = u by group]
      exact hu
    have h1 := Subgroup.mem_centralizer_iff.mp (he₀ hz') _ hfu
    calc u * z = f⁻¹ * ((f * u * f⁻¹) * (f * z * f⁻¹)) * f := by group
      _ = f⁻¹ * ((f * z * f⁻¹) * (f * u * f⁻¹)) * f := by rw [h1]
      _ = z * u := by group
  have hab := h.gamma_comm_abs (key e he) (key e' he')
  intro a ha b hb
  have ha' : f⁻¹ * a * f ∈ conjSubgroup (f⁻¹ * e) (omegaOneSub B) := by
    rw [mem_conjSubgroup, show (f⁻¹ * e)⁻¹ * (f⁻¹ * a * f) * (f⁻¹ * e) = e⁻¹ * a * e by group]
    exact mem_conjSubgroup.mp ha
  have hb' : f⁻¹ * b * f ∈ conjSubgroup (f⁻¹ * e') (omegaOneSub B) := by
    rw [mem_conjSubgroup, show (f⁻¹ * e')⁻¹ * (f⁻¹ * b * f) * (f⁻¹ * e') = e'⁻¹ * b * e' by group]
    exact mem_conjSubgroup.mp hb
  have h2 := hab _ ha' _ hb'
  calc a * b = f * ((f⁻¹ * a * f) * (f⁻¹ * b * f)) * f⁻¹ := by group
    _ = f * ((f⁻¹ * b * f) * (f⁻¹ * a * f)) * f⁻¹ := by rw [h2]
    _ = b * a := by group

theorem starData_of_not_star {g : G}
    (hg : conjSubgroup g (omegaTwoSub B) ≤ Subgroup.centralizer (omegaTwoSub B : Set G))
    {A : Subgroup G} (hA : A ∈ Lam M B) {a d : G} (ha : a ∈ A)
    (hd : d ∈ conjSubgroup g (omegaOneSub B)) (hnc : a * d ≠ d * a) :
    ∃ m α x : G, R2StarData h g m α x := by
  have hCen := CFSG.CGT.T75N.benderCenterInput
  have hU := CFSG.CGT.T75N.unitaryTwoGenerationInput
  obtain ⟨m, hAm, hAM⟩ := hA
  subst hAm
  have ha1 : a ≠ 1 := fun e => hnc (by rw [e, one_mul, mul_one])
  have hd1 : d ≠ 1 := fun e => hnc (by rw [e, one_mul, mul_one])
  have haa : a * a = 1 := Pair.sq_conj_B0 h ha
  have hdd : d * d = 1 := Pair.sq_conj_B0 h hd
  have hVe : ∀ v ∈ omegaOneSub B, v * v = 1 := fun v hv => Pair.sq_B0 h hv
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hag : conjSubgroup (a * g) (omegaTwoSub B) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := h.conj_cent_le (hAM ha) hg
  have hda : a * d * a⁻¹ ∈ conjSubgroup (a * g) (omegaOneSub B) := by
    rw [mem_conjSubgroup, show (a * g)⁻¹ * (a * d * a⁻¹) * (a * g) = g⁻¹ * d * g by group]
    exact mem_conjSubgroup.mp hd
  have hcomm : d * (a * d * a⁻¹) = (a * d * a⁻¹) * d :=
    h.gamma_comm_abs hg hag d hd _ hda
  have hxx : (a * d * a⁻¹) * (a * d * a⁻¹) = 1 := by
    calc (a * d * a⁻¹) * (a * d * a⁻¹) = a * (d * d) * a⁻¹ := by group
      _ = 1 := by rw [hdd]; group
  have h2 : (a * d) * (a * d) = (a * d * a⁻¹) * d := by
    rw [hai]
    group
  have h4 : (a * d) ^ 4 = 1 := by
    have e4 : (a * d) ^ 4 = ((a * d) * (a * d)) * ((a * d) * (a * d)) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e4, h2]
    calc (a * d * a⁻¹) * d * ((a * d * a⁻¹) * d)
        = (a * d * a⁻¹) * (d * (a * d * a⁻¹)) * d := by group
      _ = (a * d * a⁻¹) * ((a * d * a⁻¹) * d) * d := by rw [hcomm]
      _ = ((a * d * a⁻¹) * (a * d * a⁻¹)) * (d * d) := by group
      _ = 1 := by rw [hxx, hdd, one_mul]
  have hne2 : (a * d) * (a * d) ≠ 1 := fun e => hnc (comm_of_mul_mul_self haa hdd e)
  have hord : orderOf (a * d) = 4 := by
    have hdvd : orderOf (a * d) ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h4
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact hne2 (by rw [hk', one_mul])
    · exfalso
      apply hne2
      have := pow_orderOf_eq_one (a * d)
      rw [hk', pow_one] at this
      rw [← sq]
      exact this
    · rw [hk']
      norm_num
  have hall : ∀ x ∈ conjSubgroup m (omegaOneSub B), x ≠ 1 → ∀ y ∈ conjSubgroup g (omegaOneSub B),
      y ≠ 1 → orderOf (x * y) = 4 := fun x hx hx1 y hy hy1 =>
    orderOf_mul_eq_four hVe h.root ha ha1 hd hd1 hord hx hx1 hy hy1
  have hΩ : omegaOneSub (conjSubgroup (m * g⁻¹) (conjSubgroup g (omegaTwoSub B))) =
      conjSubgroup m (omegaOneSub B) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right, Pair.omegaOne_conj_U h m]
  have K : Core31 (conjSubgroup g (omegaTwoSub B)) (m * g⁻¹) :=
    { comm := Pair.comm_conj_U h g
      two := (Pair.isPGroup_U h).map (MulAut.conj g).toMonoidHom
      ti := isTI_conjSubgroup h.s3hyp.ti g
      exp := Pair.pow_four_conj h g
      exp_ne := Pair.exists_sq_ne_conj h g
      card4 := by rw [Pair.omegaOne_conj_U h g, Pair.card_conj_B0 h g]
      ord := fun α' hα' hα1' β hβ hβ1 => by
        rw [hΩ] at hα'
        rw [Pair.omegaOne_conj_U h g] at hβ
        exact hall α' hα' hα1' β hβ hβ1 }
  obtain ⟨α, hα, hα1, hncα, x, hx, hxC⟩ := K.exists_data31 hCen hU
  have D31 : Data31 (conjSubgroup g (omegaTwoSub B)) (m * g⁻¹) α x :=
    ⟨K, hα, hα1, hncα, hx, hxC⟩
  have hαM : α ∈ M := by
    rw [hΩ] at hα
    exact hAM hα
  have hαg : conjSubgroup α (conjSubgroup g (omegaTwoSub B)) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := by
    rw [← conjSubgroup_mul]
    exact h.conj_cent_le hαM hg
  have hX : conjSubgroup g (omegaTwoSub B) ⊔ conjSubgroup α (conjSubgroup g (omegaTwoSub B)) ≤
      Subgroup.centralizer (omegaTwoSub B : Set G) := sup_le hg hαg
  refine ⟨m, α, x, ?_⟩
  exact
    { centr := hg
      lam := hAM
      data31 := D31
      cent_X := hX
      cent_C := fun z hz => by
        refine hX ?_
        have hz' : x⁻¹ * z * x ∈ conjSubgroup g (omegaTwoSub B) := mem_conjSubgroup.mp hz
        have hxz : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        rw [hxz]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (Subgroup.mem_sup_left hz'))
          (Subgroup.inv_mem _ hx)
      inf_cent := fun a' ha' hC => by
        by_contra ha1'
        have hΔ := h.delta_of_ne_one ha' ha1' hC
        exact hnc (h.gamma_comm_abs hΔ hg a ha d hd)
      gamma_comm := fun f e e' he he' => h.gamma_comm f e e' he he'
      comm_of_cent := fun f c hf => h.comm_of_cent hf }

end R2

theorem r2Star_of_local (hL : R2StarLocal) : R2Star := by
  intro G _ _ M B h g hg A hA a ha d hd
  by_contra hnc
  obtain ⟨m, α, x, D⟩ := R2.starData_of_not_star h hg hA ha hd hnc
  exact hL G M B h g m α x D

theorem r2Weak_of_local (hL : R2StarLocal) : R2Weak :=
  r2Weak_of_star (r2Star_of_local hL)

end Certificates34

end CFSG.CGT.PushingUpLit.SolKR2
