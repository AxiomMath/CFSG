module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourMod
public import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt9

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise MatrixGroups

@[expose] def A9Center : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 9)) →
    Odd (Nat.card (Subgroup.center K)) → Subgroup.center K = ⊥

theorem exists_noncomm_alt9 : ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 0 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 0 3, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem exists_gen_of_alt9 {Λ : Type} [Group Λ] (e : Λ ≃* alternatingGroup (Fin 9)) (T : Subgroup Λ)
    (hcard : Nat.card T = 8) (hinv : ∀ x ∈ T, x * x = 1)
    (hconj : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ g : Λ, g * x * g⁻¹ = y) :
    ∃ g : Λ, T ⊔ T.map (MulAut.conj g).toMonoidHom = ⊤ := by
  classical
  let Ψ : Λ →* Equiv.Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom
  have hΨinj : Function.Injective Ψ :=
    Subtype.val_injective.comp e.injective
  have hΨalt : ∀ x : Λ, Ψ x ∈ alternatingGroup (Fin 9) := fun x => (e x).2
  set E : Subgroup (Equiv.Perm (Fin 9)) := T.map Ψ with hE
  have hEalt : E ≤ alternatingGroup (Fin 9) := by
    rintro _ ⟨x, -, rfl⟩
    exact hΨalt x
  have hEcard : Nat.card E = 8 := by
    rw [hE, Subgroup.card_map_of_injective hΨinj, hcard]
  have hEinv : ∀ a ∈ E, a * a = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hinv x hx, map_one]
  have hEconj : ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ π ∈ alternatingGroup (Fin 9), π * x * π⁻¹ = y := by
    rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨y, hy, rfl⟩ hy1
    have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨g, hg⟩ := hconj x hx hx1' y hy hy1'
    refine ⟨Ψ g, hΨalt g, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  obtain ⟨p, hpfix, hpreg⟩ := exists_regular_alt9 E hEalt hEcard hEinv hEconj
  obtain ⟨g₉, hg₉, hgen⟩ := exists_gen_alt9 E hEalt p hpfix hpreg hEinv
  refine ⟨e.symm ⟨g₉, hg₉⟩, ?_⟩
  apply Subgroup.map_injective hΨinj
  rw [Subgroup.map_sup, ← hE]
  have h1 : (T.map (MulAut.conj (e.symm ⟨g₉, hg₉⟩)).toMonoidHom).map Ψ =
      E.map (MulAut.conj g₉).toMonoidHom := by
    rw [hE, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [Ψ, MulAut.conj_apply]
  rw [h1, hgen, Subgroup.map_top]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm ⟨x, hx⟩, by simp [Ψ]⟩
  · rintro ⟨y, rfl⟩
    exact hΨalt y

theorem exists_e9_of_alt9 {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 9)) {c : K}
    (hc : orderOf c = 9) :
    ∃ x g₁ g₂ g₃ : K, x ^ 3 = 1 ∧ c ^ 3 * x = x * c ^ 3 ∧ x = g₁ * c ^ 3 * g₁⁻¹ ∧
      c ^ 3 * x = g₂ * c ^ 3 * g₂⁻¹ ∧ c ^ 3 * x ^ 2 = g₃ * c ^ 3 * g₃⁻¹ := by
  have hc' : orderOf (e c) = 9 := by rw [MulEquiv.orderOf_eq]; exact hc
  obtain ⟨x, g₁, g₂, g₃, h1, h2, h3, h4, h5⟩ := exists_e9_alt9 (e c) hc'
  refine ⟨e.symm x, e.symm g₁, e.symm g₂, e.symm g₃, ?_, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, h1, map_one]
  · apply e.injective
    simp only [map_mul, map_pow, MulEquiv.apply_symm_apply]
    exact h2
  · apply e.injective
    simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
    exact h3
  · apply e.injective
    simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
    exact h4
  · apply e.injective
    simp only [map_mul, map_pow, map_inv, MulEquiv.apply_symm_apply]
    exact h5

variable {G : Type} [Group G] [Finite G]

theorem eight_sl_not_alt9 (hZ : A9Center) {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal]
    (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hA : Nonempty (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T) ≃*
      alternatingGroup (Fin 9))) : False := by
  classical
  obtain ⟨hn2, hsimple, hlist, hstd, hcardTh, hperf, ρ, ι', hρval, hι'mk, hι'inj, hWCb, hZodd⟩ :=
    eight_sl_ident h hn hnat hS h215 hL
  have h9 := hstd.card_alternating (k := 9) (by norm_num) (by norm_num) hA
  have hn3 : n = 3 := by
    have h2n : 2 ^ n = 2 ^ 3 := by rw [← hcardTh, h9]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn3
  have hJbK : jBar R T ≤ jBarClosure R T := Subgroup.le_normalClosure
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hidx := h.index_cV_jBar hn hnat
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  obtain ⟨e⟩ := hA
  generalize hKdef : jBarClosure R T = K at *
  have hZ1 : Subgroup.center ↥K = ⊥ := by
    refine hZ ↥K ⟨⟨hperf⟩, hsimple, ?_⟩ ⟨e⟩ hZodd
    obtain ⟨u, v, huv⟩ := exists_noncomm_alt9
    exact ⟨e.symm u, e.symm v, fun hh => huv (by simpa using congrArg e hh)⟩
  have hqinj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ1]
  let e' : ↥K ≃* alternatingGroup (Fin 9) :=
    (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥K))
      ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans e
  have he' : ∀ k : ↥K, e' k = e (QuotientGroup.mk' (Subgroup.center ↥K) k) := fun k => rfl
  obtain ⟨c₀, hc₀⟩ := exists_orderOf_nine
  set cbar : ↥Y ⧸ pCore 2 ↥Y := φ.symm c₀ with hcbar
  have hcbar9 : orderOf cbar = 9 := by rw [hcbar, MulEquiv.orderOf_eq]; exact hc₀
  obtain ⟨ct, hct⟩ := QuotientGroup.mk_surjective cbar
  have hct9 : ct ^ 9 ∈ pCore 2 ↥Y := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_pow, hct, ← hcbar9]
    exact pow_orderOf_eq_one _
  have hρ9 : ρ (ct ^ 9) = 1 := by
    apply Subtype.ext
    rw [hρval]
    have hmem : ((ct ^ 9 : ↥Y) : G) ∈ R := hOY ⟨ct ^ 9, hct9, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  set cK : ↥K := ρ ct with hcK
  have hcK9 : cK ^ 9 = 1 := by rw [hcK, ← map_pow]; exact hρ9
  have hecK : e' cK = e (ι' cbar) := by
    rw [he', hcK, ← hct, ← hι'mk]
  have hcKord : orderOf cK = 9 := by
    rw [← MulEquiv.orderOf_eq e' cK, hecK, MulEquiv.orderOf_eq, orderOf_injective ι' hι'inj cbar,
      hcbar9]
  obtain ⟨xK, g1, g2, g3, hxK3, hxKc, hx1, hx2, hx3⟩ := exists_e9_of_alt9 e' hcKord
  set q : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hq
  set Jp : Subgroup ↥K := (jBar R T).subgroupOf K with hJp
  have hJpcard : Nat.card Jp = 8 := by
    have := hcardTh
    rw [Subgroup.card_map_of_injective hqinj] at this
    omega
  have hJpinv : ∀ x ∈ Jp, x * x = 1 := by
    intro x hx
    have hqx : q x ∈ Subgroup.map q Jp := ⟨x, hx, rfl⟩
    have h2 := hWCb.1.2 _ hqx
    apply hqinj
    rw [map_mul, map_one, ← sq]
    exact h2
  have hJpconj : ∀ x ∈ Jp, x ≠ 1 → ∀ y ∈ Jp, y ≠ 1 → ∃ g : ↥K, g * x * g⁻¹ = y := by
    intro x hx hx1 y hy hy1
    have hqx : q x ∈ Subgroup.map q Jp := ⟨x, hx, rfl⟩
    have hqy : q y ∈ Subgroup.map q Jp := ⟨y, hy, rfl⟩
    have hqx1 : q x ≠ 1 := fun hh => hx1 (hqinj (by rw [hh, map_one]))
    have hqy1 : q y ≠ 1 := fun hh => hy1 (hqinj (by rw [hh, map_one]))
    obtain ⟨g, -, hg⟩ := hstd.transitive (q x) hqx hqx1 (q y) hqy hqy1
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact ⟨g', hqinj (by rw [map_mul, map_mul, map_inv]; exact hg)⟩
  obtain ⟨k₀, hk₀⟩ := exists_gen_of_alt9 e' Jp hJpcard hJpinv hJpconj
  have hKgen : K = jBar R T ⊔ (jBar R T).map (MulAut.conj (k₀ : G ⧸ R)).toMonoidHom := by
    have h1 := congrArg (Subgroup.map K.subtype) hk₀
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
    have h2 : Jp.map K.subtype = jBar R T := by
      rw [hJp, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJbK]
    have h3 : (Jp.map (MulAut.conj k₀).toMonoidHom).map K.subtype =
        (jBar R T).map (MulAut.conj (k₀ : G ⧸ R)).toMonoidHom := by
      rw [Subgroup.map_map, ← h2, Subgroup.map_map]
      congr 1
    rw [h2, h3] at h1
    exact h1.symm
  have hcVK : (h.cV K).index ≤ 2 ^ 6 := by
    rw [hKgen, h.cV_sup]
    calc (h.cV (jBar R T) ⊓ h.cV ((jBar R T).map (MulAut.conj (k₀ : G ⧸ R)).toMonoidHom)).index
        ≤ (h.cV (jBar R T)).index *
          (h.cV ((jBar R T).map (MulAut.conj (k₀ : G ⧸ R)).toMonoidHom)).index :=
          Subgroup.index_inf_le
      _ = 2 ^ 3 * 2 ^ 3 := by rw [h.index_cV_conj, hidx]
      _ = 2 ^ 6 := by norm_num
  have hord3 : (c₀ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 from rfl, ← hc₀]
    exact pow_orderOf_eq_one c₀
  have hne1 : c₀ ^ 3 ≠ 1 := fun hh => by
    have := orderOf_dvd_of_pow_eq_one hh
    rw [hc₀] at this
    omega
  have hfixvec : ∀ w : Fin 2 → GaloisField 2 3,
      ((φ (↑(ct ^ 3) : ↥Y ⧸ pCore 2 ↥Y) : SL(2, GaloisField 2 3)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 3)).mulVec w = w → w = 0 := by
    intro w hw
    have hφ3 : φ (↑(ct ^ 3) : ↥Y ⧸ pCore 2 ↥Y) = c₀ ^ 3 := by
      rw [QuotientGroup.mk_pow, hct, hcbar, map_pow, MulEquiv.apply_symm_apply]
    rw [hφ3] at hw
    exact fixed_vec_eq_zero_of_order_three hord3 hne1 w hw
  have hle := h.le_index_autFixSub φ ψ hψs hψe (ct ^ 3) hfixvec
  have hF8 : Nat.card (GaloisField 2 3) = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [GaloisField.card 2 3 (by norm_num)]; norm_num
  rw [hF8] at hle
  have hbeq : ((cK ^ 3 : ↥K) : G ⧸ R) = QuotientGroup.mk ((ct ^ 3 : ↥Y) : G) := by
    rw [hcK, ← map_pow, hρval]; rfl
  have hc : ∀ a b : ↥(omegaOneCenterIn R), a * b = b * a := omegaOneCenterIn_comm R
  have hV : ∀ v : ↥(omegaOneCenterIn R), v * v = 1 := omegaOneCenterIn_mul_self R
  have hmemΓ : ∀ k : ↥K, h.vAct (k : G ⧸ R) ∈ K.map h.vAct := fun k => ⟨k, k.2, rfl⟩
  have hb3 : (h.vAct ((cK ^ 3 : ↥K) : G ⧸ R)) ^ 3 = 1 := by
    have : (cK ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hcK9
    rw [← map_pow, ← Subgroup.coe_pow, this]
    simp
  have hxcube : (h.vAct (xK : G ⧸ R)) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hxK3]
    simp
  have hcomm : Commute (h.vAct ((cK ^ 3 : ↥K) : G ⧸ R)) (h.vAct (xK : G ⧸ R)) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hxKc]
  have hxc : ∃ g ∈ K.map h.vAct, h.vAct (xK : G ⧸ R) =
      g * h.vAct ((cK ^ 3 : ↥K) : G ⧸ R) * g⁻¹ := by
    refine ⟨h.vAct (g1 : G ⧸ R), hmemΓ g1, ?_⟩
    have := congrArg (fun k : ↥K => h.vAct (k : G ⧸ R)) hx1
    simpa [map_mul, map_inv] using this
  have hbxc : ∃ g ∈ K.map h.vAct, h.vAct ((cK ^ 3 : ↥K) : G ⧸ R) * h.vAct (xK : G ⧸ R) =
      g * h.vAct ((cK ^ 3 : ↥K) : G ⧸ R) * g⁻¹ := by
    refine ⟨h.vAct (g2 : G ⧸ R), hmemΓ g2, ?_⟩
    have := congrArg (fun k : ↥K => h.vAct (k : G ⧸ R)) hx2
    simpa [map_mul, map_inv] using this
  have hbx2c : ∃ g ∈ K.map h.vAct, h.vAct ((cK ^ 3 : ↥K) : G ⧸ R) * h.vAct (xK : G ⧸ R) ^ 2 =
      g * h.vAct ((cK ^ 3 : ↥K) : G ⧸ R) * g⁻¹ := by
    refine ⟨h.vAct (g3 : G ⧸ R), hmemΓ g3, ?_⟩
    have := congrArg (fun k : ↥K => h.vAct (k : G ⧸ R)) hx3
    simpa [map_mul, map_inv, map_pow] using this
  have hidx' : (autFixGrp (K.map h.vAct)).index ≤
      (autFixSub (h.vAct ((cK ^ 3 : ↥K) : G ⧸ R))).index := by
    rw [hbeq]
    exact hcVK.trans (by norm_num at hle ⊢; exact hle)
  have hres := e9_count hc hV (K.map h.vAct) (hmemΓ (cK ^ 3)) hb3 hxcube hcomm hxc hbxc hbx2c hidx'
  rw [hbeq] at hres
  have h1 : (autFixSub (h.vAct (QuotientGroup.mk ((ct ^ 3 : ↥Y) : G)))).index = 1 := by
    rw [hres]; exact Subgroup.index_top
  rw [h1] at hle
  norm_num at hle

end CFSG.CGT.PushingUpLit.CGT6
