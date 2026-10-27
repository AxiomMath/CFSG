module

public import CFSG.GH74.GLS.Bg.TwoGroups.L27A
public import CFSG.GH74.GLS.Bg.TwoGroups.Basic
public import CFSG.GH74.GLS.Bg.TwoGroups.L26Cfg

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L27

open L26

variable {T : Type} [Group T] {t : T} {α : MulAut T} {E : Subgroup T}

theorem Cfg7.E2 (cfg : Cfg7 T t α E) : ∀ e ∈ E, e * e = 1 := fun e he =>
  cfg.C2 e (cfg.EC e he)

theorem Cfg7.Ec (cfg : Cfg7 T t α E) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
  cfg.Cab a b (cfg.EC a ha) (cfg.EC b hb)

theorem Cfg7.klein (cfg : Cfg7 T t α E) (z : T) (hz : z ∈ E) (hz1 : z ≠ 1) :
    ∀ w ∈ E, w = 1 ∨ w = z ∨ w = α z ∨ w = z * α z := by
  have hαz : α z ∈ E := cfg.Einv z hz
  have hαz1 : α z ≠ 1 := fun h => hz1 (by simpa using h)
  have hne : α z ≠ z := fun h => hz1 (cfg.Efpf z hz h)
  have hprod1 : z * α z ≠ 1 := by
    intro h
    apply hne
    have : α z = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (cfg.E2 z hz)).symm
  exact L23.subgroup_card_four E cfg.Ecard z (α z) (z * α z) hz hαz (mul_mem hz hαz)
    (Ne.symm hz1) (Ne.symm hαz1) (Ne.symm hprod1) (Ne.symm hne)
    (fun h => hαz1 (mul_eq_left.mp h.symm)) (fun h => hz1 (mul_eq_right.mp h.symm))

theorem Cfg7.fixedC (cfg : Cfg7 T t α E) (c : T) (hc : t * c = c * t) (hfix : α c = c) :
    c = 1 ∨ c = t := by
  rcases cfg.CE c hc with hE | ⟨e, he, rfl⟩
  · exact Or.inl (cfg.Efpf c hE hfix)
  · right
    rw [map_mul, cfg.αt] at hfix
    have h1 : α e = e := mul_left_cancel hfix
    rw [cfg.Efpf e he h1, mul_one]

variable [Finite T]

theorem Cfg7.fixed (cfg : Cfg7 T t α E) (g : T) (hg : α g = g) : g = 1 ∨ g = t := by
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  right
  set D := fixSub α with hD
  have htD : t ∈ D := cfg.αt
  have hgD : g ∈ D := hg
  have hpD : IsPGroup 2 ↥D := cfg.p2.to_subgroup D
  have : Nontrivial ↥D := ⟨⟨⟨t, htD⟩, 1, fun h => cfg.t1 (congrArg Subtype.val h)⟩⟩
  have hcn : Nontrivial (Subgroup.center ↥D) := IsPGroup.center_nontrivial hpD
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center ↥D)
  have hzc : ∀ d : ↥D, d * (z : ↥D) = (z : ↥D) * d := fun d => Subgroup.mem_center_iff.mp z.2 d
  have hzt : ((z : ↥D) : T) = t := by
    have h1 : t * ((z : ↥D) : T) = ((z : ↥D) : T) * t :=
      congrArg Subtype.val (hzc ⟨t, htD⟩)
    have h2 : α ((z : ↥D) : T) = ((z : ↥D) : T) := (z : ↥D).2
    rcases cfg.fixedC _ h1 h2 with h3 | h3
    · exact absurd (Subtype.ext (Subtype.ext h3)) hz
    · exact h3
  have h1 : t * g = g * t := by
    have := congrArg Subtype.val (hzc ⟨g, hgD⟩)
    change g * ((z : ↥D) : T) = ((z : ↥D) : T) * g at this
    rw [hzt] at this
    exact this.symm
  rcases cfg.fixedC g h1 hg with h | h
  · exact absurd h hg1
  · exact h

theorem Cfg7.E_central (cfg : Cfg7 T t α E) (hnc : ¬ ∀ g : T, t * g = g * t) :
    ∀ e ∈ E, ∀ g : T, e * g = g * e := by
  have hcn : Nontrivial (Subgroup.center T) := by
    have : Nontrivial T := ⟨⟨t, 1, cfg.t1⟩⟩
    exact IsPGroup.center_nontrivial cfg.p2
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center T)
  have hzc : ∀ g : T, g * (z : T) = (z : T) * g := fun g => Subgroup.mem_center_iff.mp z.2 g
  have hz1 : (z : T) ≠ 1 := fun h => hz (Subtype.ext h)
  have hαz : α (z : T) ∈ Subgroup.center T := center_invariant α (z : T) z.2
  have key : ∃ z' ∈ E, z' ≠ 1 ∧ z' ∈ Subgroup.center T := by
    rcases cfg.CE z (hzc t) with hE | ⟨e, he, hze⟩
    · exact ⟨z, hE, hz1, z.2⟩
    · by_cases he1 : e = 1
      · exfalso
        apply hnc
        intro g
        have : (z : T) = t := by rw [hze, he1, mul_one]
        rw [← this]
        exact (hzc g).symm
      · refine ⟨e⁻¹ * α e, mul_mem (inv_mem he) (cfg.Einv e he), ?_, ?_⟩
        · intro h
          apply he1
          apply cfg.Efpf e he
          have h' : e⁻¹ * α e = 1 := h
          calc α e = e * (e⁻¹ * α e) := by group
            _ = e := by rw [h', mul_one]
        · have h1 : (z : T)⁻¹ * α z ∈ Subgroup.center T :=
            mul_mem (inv_mem z.2) hαz
          have h2 : (z : T)⁻¹ * α z = e⁻¹ * α e := by
            rw [hze, map_mul, cfg.αt]
            group
          rw [← h2]
          exact h1
  obtain ⟨z', hz'E, hz'1, hz'c⟩ := key
  have hz'c' : ∀ g : T, g * z' = z' * g := fun g => Subgroup.mem_center_iff.mp hz'c g
  have hαz'c : α z' ∈ Subgroup.center T := center_invariant α z' hz'c
  have hαz'c' : ∀ g : T, g * α z' = α z' * g := fun g => Subgroup.mem_center_iff.mp hαz'c g
  intro e he g
  rcases cfg.klein z' hz'E hz'1 e he with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact (hz'c' g).symm
  · rw [h]; exact (hαz'c' g).symm
  · rw [h]
    calc z' * α z' * g = z' * (α z' * g) := by rw [mul_assoc]
      _ = z' * (g * α z') := by rw [← hαz'c' g]
      _ = (z' * g) * α z' := by rw [← mul_assoc]
      _ = (g * z') * α z' := by rw [← hz'c' g]
      _ = g * (z' * α z') := by rw [mul_assoc]

theorem Cfg7.normal (cfg : Cfg7 T t α E) (hnc : ¬ ∀ g : T, t * g = g * t) : E.Normal :=
  ⟨fun n hn g => by
    have := cfg.E_central hnc n hn g
    have h : g * n * g⁻¹ = n := by rw [← this]; group
    rw [h]
    exact hn⟩


theorem Cfg7.sq_mem (cfg : Cfg7 T t α E) [E.Normal] (hnc : ¬ ∀ g : T, t * g = g * t) (s : T)
    (hs : (QuotientGroup.mk t : T ⧸ E) * QuotientGroup.mk s =
      QuotientGroup.mk s * QuotientGroup.mk t) : s * s ∈ E := by
  have hcen := cfg.E_central hnc
  have hu : (t * s)⁻¹ * (s * t) ∈ E := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hs
    exact QuotientGroup.eq.mp hs
  set u := (t * s)⁻¹ * (s * t) with hudef
  have hst : s * t = t * s * u := by rw [hudef]; group
  have hu_c : ∀ g : T, u * g = g * u := cfg.E_central hnc u hu
  have hss : (s * s) * t = t * (s * s) := by
    calc (s * s) * t = s * (s * t) := by rw [mul_assoc]
      _ = s * (t * s * u) := by rw [hst]
      _ = (s * t) * s * u := by simp only [mul_assoc]
      _ = (t * s * u) * s * u := by rw [hst]
      _ = t * s * (u * s) * u := by simp only [mul_assoc]
      _ = t * s * (s * u) * u := by rw [hu_c s]
      _ = t * (s * s) * (u * u) := by simp only [mul_assoc]
      _ = t * (s * s) := by rw [cfg.E2 u hu, mul_one]
  rcases cfg.CE (s * s) hss.symm with h | ⟨e, he, hee⟩
  · exact h
  · exfalso
    have h1 : s * (t * e) = (t * e) * s := by
      rw [← hee]
      exact (mul_assoc s s s).symm
    have h3 : s * t * e = t * s * e := by
      calc s * t * e = s * (t * e) := by rw [mul_assoc]
        _ = (t * e) * s := h1
        _ = t * (e * s) := by rw [mul_assoc]
        _ = t * (s * e) := by rw [hcen e he s]
        _ = t * s * e := by rw [mul_assoc]
    have h2 : s * t = t * s := mul_right_cancel h3
    have hss1 : s * s = 1 := cfg.C2 s h2.symm
    have : t = e⁻¹ := by
      calc t = t * e * e⁻¹ := by group
        _ = s * s * e⁻¹ := by rw [← hee]
        _ = e⁻¹ := by rw [hss1, one_mul]
    exact cfg.tE (this ▸ inv_mem he)

theorem Cfg7.quot_fix (cfg : Cfg7 T t α E) [E.Normal] (x : T ⧸ E)
    (hx : quotAut E α cfg.Einv x = x) : x = 1 ∨ x = QuotientGroup.mk t := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
    rw [quotAut_mk] at hx
    have hg : g⁻¹ * α g ∈ E := QuotientGroup.eq.mp hx.symm
    obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 cfg.p2 α 1 (by rw [pow_one]; exact cfg.a3) E
      cfg.Einv g hg
    have hmk : (QuotientGroup.mk g : T ⧸ E) = QuotientGroup.mk s := QuotientGroup.eq.mpr hs
    rcases cfg.fixed s hαs with h | h
    · left
      rw [hmk, h, QuotientGroup.mk_one]
    · right
      rw [hmk, h]

theorem Cfg7.quot_ne_one (cfg : Cfg7 T t α E) [E.Normal] (hnc : ¬ ∀ g : T, t * g = g * t) :
    quotAut E α cfg.Einv ≠ 1 := by
  intro h1
  apply hnc
  intro g
  have hg : g⁻¹ * α g ∈ E := by
    have := congrArg (fun s : MulAut (T ⧸ E) => s (QuotientGroup.mk g)) h1
    simp only [quotAut_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.mp this.symm
  obtain ⟨s, hs, hαs⟩ := exists_fixed_coset3 cfg.p2 α 1 (by rw [pow_one]; exact cfg.a3) E
    cfg.Einv g hg
  have hst : t * s = s * t := by
    rcases cfg.fixed s hαs with h | h
    · rw [h]
      simp
    · rw [h]
  have he := cfg.EC _ hs
  have h3 : t * g⁻¹ * s = g⁻¹ * t * s := by
    calc t * g⁻¹ * s = t * (g⁻¹ * s) := by rw [mul_assoc]
      _ = (g⁻¹ * s) * t := he
      _ = g⁻¹ * (s * t) := by rw [mul_assoc]
      _ = g⁻¹ * (t * s) := by rw [hst]
      _ = g⁻¹ * t * s := by rw [mul_assoc]
  have h4 : Commute t g⁻¹ := mul_right_cancel h3
  have h5 := h4.inv_right
  rw [inv_inv] at h5
  exact h5.eq

theorem Cfg7.quot_card (cfg : Cfg7 T t α E) [E.Normal] (hnc : ¬ ∀ g : T, t * g = g * t) :
    Nat.card (Subgroup.centralizer ({(QuotientGroup.mk t : T ⧸ E)} : Set (T ⧸ E))) = 8 := by
  classical
  set Cb := Subgroup.centralizer ({(QuotientGroup.mk t : T ⧸ E)} : Set (T ⧸ E)) with hCb
  set αb := quotAut E α cfg.Einv with hαb
  have hpb : IsPGroup 2 (T ⧸ E) :=
    cfg.p2.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  have htb1 : (QuotientGroup.mk t : T ⧸ E) ≠ 1 := fun h => cfg.tE ((QuotientGroup.eq_one_iff t).mp h)
  have hαb3 : αb ^ 3 = 1 := quotAut_pow_eq_one E α cfg.Einv 3 cfg.a3
  have hαbt : αb (QuotientGroup.mk t) = QuotientGroup.mk t := by rw [hαb, quotAut_mk, cfg.αt]
  have hinvC : ∀ x ∈ Cb, αb x ∈ Cb := cent_inv _ αb hαbt
  have hmod := card_fix_modEq3 αb 1 (by rw [pow_one]; exact hαb3) Cb hinvC
  have htCb : (QuotientGroup.mk t : T ⧸ E) ∈ Cb := mem_cent.mpr rfl
  let x₀ : {v : ↥Cb // αb v = v} := ⟨1, map_one αb⟩
  let y₀ : {v : ↥Cb // αb v = v} := ⟨⟨QuotientGroup.mk t, htCb⟩, hαbt⟩
  have hfix2 : Nat.card {v : ↥Cb // αb v = v} = 2 := by
    refine (Nat.card_eq_two_iff' x₀).mpr ⟨y₀, ?_, ?_⟩
    · intro h
      exact htb1 (congrArg (fun v : {v : ↥Cb // αb v = v} => ((v.1 : ↥Cb) : T ⧸ E)) h)
    · intro y hy
      rcases cfg.quot_fix y.1.1 y.2 with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy
      · exact Subtype.ext (Subtype.ext h)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hpb.to_subgroup Cb)
  have hle : Nat.card Cb ≤ 8 := le_of_le_of_eq (ig_9_16 T E t) cfg.Ccard
  have hmod2 : Nat.card Cb % 3 = 2 := by
    have h1 : Nat.card Cb % 3 = Nat.card {v : ↥Cb // αb v = v} % 3 := hmod
    rw [hfix2] at h1
    exact h1
  have hn3 : n ≤ 3 := by
    by_contra hcon
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : Nat.card Cb = 8 ∨ Nat.card Cb = 2 := by
    interval_cases n
    · rw [pow_zero] at hn
      omega
    · right
      rw [hn]
      norm_num
    · rw [hn] at hmod2
      norm_num at hmod2
    · left
      rw [hn]
      norm_num
  rcases h8 with h8 | h2
  · exact h8
  · exfalso
    have hz : Nontrivial (T ⧸ E) := ⟨⟨QuotientGroup.mk t, 1, htb1⟩⟩
    have hcn : Nontrivial (Subgroup.center (T ⧸ E)) := IsPGroup.center_nontrivial hpb
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (T ⧸ E))
    have hzcomm : ∀ g : T ⧸ E, g * (z : T ⧸ E) = (z : T ⧸ E) * g := fun g =>
      Subgroup.mem_center_iff.mp z.2 g
    have hzC : (z : T ⧸ E) ∈ Cb := mem_cent.mpr (hzcomm _)
    obtain ⟨y0, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Cb)).mp h2
    have hz_eq : (z : T ⧸ E) = QuotientGroup.mk t := by
      have e1 : (⟨(z : T ⧸ E), hzC⟩ : ↥Cb) = y0 :=
        huniq _ (fun h => hz1 (Subtype.ext (congrArg (fun v : ↥Cb => (v : T ⧸ E)) h)))
      have e2 : (⟨QuotientGroup.mk t, htCb⟩ : ↥Cb) = y0 :=
        huniq _ (fun h => htb1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (e1.trans e2.symm)
    have htcen : ∀ g : T ⧸ E, QuotientGroup.mk t * g = g * QuotientGroup.mk t := by
      intro g
      rw [← hz_eq]
      exact (hzcomm g).symm
    have hCtop : Cb = ⊤ := eq_top_iff.mpr fun x _ => mem_cent.mpr (htcen x)
    rw [hCtop, Subgroup.card_top] at h2
    have hT8 : Nat.card T = 8 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup E
      rw [h2, cfg.Ecard] at this
      omega
    have hCT : Subgroup.centralizer ({t} : Set T) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [cfg.Ccard, hT8]
    apply hnc
    intro g
    have : g ∈ Subgroup.centralizer ({t} : Set T) := by
      rw [hCT]
      exact Subgroup.mem_top g
    exact mem_cent.mp this

theorem Cfg7.hyp7_quot (cfg : Cfg7 T t α E) [E.Normal] (hnc : ¬ ∀ g : T, t * g = g * t) :
    Hyp7 (T ⧸ E) (QuotientGroup.mk t) (quotAut E α cfg.Einv) := by
  have hpb : IsPGroup 2 (T ⧸ E) :=
    cfg.p2.of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  have hsq : ∀ x : T ⧸ E, (QuotientGroup.mk t : T ⧸ E) * x = x * QuotientGroup.mk t →
      x * x = 1 := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | _ s =>
      have := cfg.sq_mem hnc s hx
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).mpr this
  refine
    { p2 := hpb
      t2 := ?_
      t1 := fun h => cfg.tE ((QuotientGroup.eq_one_iff t).mp h)
      Cab := ?_
      C2 := hsq
      Ccard := cfg.quot_card hnc
      a3 := quotAut_pow_eq_one E α cfg.Einv 3 cfg.a3
      a1 := cfg.quot_ne_one hnc
      αt := by rw [quotAut_mk, cfg.αt] }
  · rw [← QuotientGroup.mk_mul, cfg.t2, QuotientGroup.mk_one]
  · intro a b ha hb
    have hab : (QuotientGroup.mk t : T ⧸ E) * (a * b) = (a * b) * QuotientGroup.mk t := by
      calc (QuotientGroup.mk t : T ⧸ E) * (a * b) = (QuotientGroup.mk t * a) * b := by
            rw [mul_assoc]
        _ = (a * QuotientGroup.mk t) * b := by rw [ha]
        _ = a * (QuotientGroup.mk t * b) := by rw [mul_assoc]
        _ = a * (b * QuotientGroup.mk t) := by rw [hb]
        _ = (a * b) * QuotientGroup.mk t := by rw [mul_assoc]
    have h1 := hsq a ha
    have h2 := hsq b hb
    have h3 := hsq (a * b) hab
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h1
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right h2
    have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h3
    rw [mul_inv_rev, ha', hb'] at hab'
    exact hab'.symm

theorem commAut_mk (E : Subgroup T) [E.Normal] (α : MulAut T) (hE : ∀ e ∈ E, α e ∈ E) (g : T)
    (hg : g ∈ commAut α) : (QuotientGroup.mk g : T ⧸ E) ∈ commAut (quotAut E α hE) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    apply Subgroup.subset_closure
    exact ⟨QuotientGroup.mk y, by
      simp only [quotAut_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  | one =>
    rw [QuotientGroup.mk_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    rw [QuotientGroup.mk_mul]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [QuotientGroup.mk_inv]
    exact inv_mem hx

theorem key7 : ∀ (n : ℕ) (T : Type) [Group T] [Finite T], Nat.card T = n →
    ∀ (t : T) (α : MulAut T), Hyp7 T t α → t ∉ commAut α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T _ _ hn t α h
    obtain ⟨E, cfg⟩ := exists_E h
    by_cases hc : ∀ g : T, t * g = g * t
    · intro ht
      have hsub : commAut α ≤ E := by
        refine (Subgroup.closure_le E).mpr ?_
        rintro _ ⟨g, rfl⟩
        rcases cfg.CE g (hc g) with hg | ⟨e, he, rfl⟩
        · exact mul_mem (inv_mem hg) (cfg.Einv g hg)
        · show (t * e)⁻¹ * α (t * e) ∈ E
          rw [map_mul, cfg.αt]
          have : (t * e)⁻¹ * (t * α e) = e⁻¹ * α e := by group
          rw [this]
          exact mul_mem (inv_mem he) (cfg.Einv e he)
      exact cfg.tE (hsub ht)
    · have hEn : E.Normal := cfg.normal hc
      have hq := cfg.hyp7_quot hc
      have hlt : Nat.card (T ⧸ E) < n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
        rw [cfg.Ecard, hn] at h1
        have : 0 < Nat.card (T ⧸ E) := Nat.card_pos
        omega
      intro ht
      exact ih _ hlt (T ⧸ E) rfl _ _ hq (commAut_mk E α cfg.Einv t ht)

theorem key7' (h : Hyp7 T t α) : t ∉ commAut α := key7 _ T rfl t α h

end L27

end CFSG.GH74.GLS.Bg.TwoGroups
