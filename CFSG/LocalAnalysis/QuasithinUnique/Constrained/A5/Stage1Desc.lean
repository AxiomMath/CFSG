module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Coord
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Subs5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4M1

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem pact_four {σ : Equiv.Perm (Fin 5)} (h : σ 4 = 4) (v : Fin 5 → ZMod 2) :
    pact σ v 4 = v 4 := by
  have h' : σ⁻¹ 4 = 4 := Equiv.Perm.inv_eq_iff_eq.mpr h.symm
  show v (σ⁻¹ 4) = v 4
  rw [h']

theorem odd_nsmul_zmod2 {n : ℕ} (hn : Odd n) (c : ZMod 2) : n • c = c := by
  have : ((n : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hn
  rw [nsmul_eq_mul, this, one_mul]

theorem K_conj {G : Type} [Group G] [Finite G] {M L : Subgroup G} {u k : G} (hu : u ∈ M ⊓ L)
    (hk : k ∈ borelK M L) : u * k * u⁻¹ ∈ borelK M L := by
  have hk' : k ∈ opResidual 2 (M ⊓ L) := by rwa [borelK, pResidualOf_eq_opResidual] at hk
  have hkML : k ∈ M ⊓ L := opResidual_le 2 _ hk'
  have := (opResidual_normal 2 (M ⊓ L)).conj_mem ⟨k, hkML⟩ (Subgroup.mem_subgroupOf.mpr hk')
    ⟨u, hu⟩
  have h2 := Subgroup.mem_subgroupOf.mp this
  rw [borelK, pResidualOf_eq_opResidual]
  exact h2

theorem mem_K_of_odd {G : Type} [Group G] [Finite G] {M L : Subgroup G} {x : G} (hx : x ∈ M ⊓ L)
    (hcop : (orderOf x).Coprime 2) : x ∈ borelK M L := by
  rw [borelK, pResidualOf_eq_opResidual]
  exact Subgroup.subset_closure ⟨hx, hcop⟩

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem U_le_R (C : StdCfg T M H S L) : blockU L ≤ baum S := by
  obtain ⟨x, hxT, hxS⟩ := C.exists_mem_T_sdiff
  intro u hu
  rw [C.F.R_eq x hxT hxS]
  exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hu)

theorem mem_M_iff (C : StdCfg T M H S L) (h : ↥H) : (h : G) ∈ M ↔ C.D.π h ∈ S4std :=
  ⟨C.pi_MH h, C.mem_M_of_pi_mem h⟩

theorem U_le_ML (C : StdCfg T M H S L) : blockU L ≤ M ⊓ L := by
  refine le_inf ?_ (blockU_le_L C.hcs)
  exact (blockU_le_S C.hcs C.hj).trans (C.hcs.sylow_inf.le.trans inf_le_right)

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem mem_iff_pi {Y : Subgroup G} (hUY : blockU L ≤ Y) (h : ↥H) :
    (h : G) ∈ Y ↔ ∃ y : ↥H, (y : G) ∈ Y ∧ C.D.π y = C.D.π h := by
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨y, hy, hπ⟩
    have hker : C.D.π (h * y⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
    have hU : ((h * y⁻¹ : ↥H) : G) ∈ blockU L := by
      rw [← C.Q_eq_U X.hTC]
      exact (C.hker _).mp hker
    have : (h : G) = ((h * y⁻¹ : ↥H) : G) * (y : G) := by simp
    rw [this]
    exact mul_mem (hUY hU) hy

theorem mem_L_iff (h : ↥H) : (h : G) ∈ L ↔ C.D.π h ∈ alternatingGroup (Fin 5) := by
  rw [X.mem_iff_pi (blockU_le_L C.hcs) h]
  constructor
  · rintro ⟨y, hy, hπ⟩
    rw [← hπ]
    have : C.D.π y = ((C.D.α ⟨y, hy⟩ : Alt5) : Equiv.Perm (Fin 5)) := C.D.hπL (y : G) hy
    rw [this]
    exact (C.D.α ⟨y, hy⟩).2
  · intro hσ
    obtain ⟨l, hl⟩ := C.D.hα ⟨C.D.π h, hσ⟩
    refine ⟨⟨l, C.D.hLH l.2⟩, l.2, ?_⟩
    have : C.D.π ⟨l, C.D.hLH l.2⟩ = ((C.D.α l : Alt5) : Equiv.Perm (Fin 5)) :=
      C.D.hπL (l : G) l.2
    rw [this]
    exact congrArg Subtype.val hl

theorem mem_S_iff (h : ↥H) : (h : G) ∈ S ↔ C.D.π h ∈ Dstd := by
  rw [X.mem_iff_pi (blockU_le_S C.hcs C.hj) h]
  constructor
  · rintro ⟨y, hy, hπ⟩
    rw [← hπ]
    exact C.pi_mem_Dstd hy
  · intro hσ
    obtain ⟨s, hs, hπ⟩ := C.exists_mem_S_pi hσ
    exact ⟨⟨s, C.hcs.sylow.le hs⟩, hs, hπ⟩

theorem mem_R_iff (h : ↥H) : (h : G) ∈ baum S ↔ C.D.π h ∈ Estd := by
  rw [X.mem_iff_pi C.U_le_R h]
  constructor
  · rintro ⟨y, hy, hπ⟩
    rw [← hπ]
    exact C.hRE y hy
  · intro hσ
    obtain ⟨r, hr, hπ⟩ := C.hRE' _ hσ
    exact ⟨⟨r, baum_le_H C.hcs hr⟩, hr, hπ⟩

theorem cw_mul (h h' : ↥H) : X.cw (h * h') = X.cw h + vact (C.D.π h) (X.cw h') := by
  have e3 : h * h' = X.emb (X.cw h + vact (C.D.π h) (X.cw h')) (C.D.π h * C.D.π h') := by
    calc h * h' = X.emb (X.cw h) (C.D.π h) * X.emb (X.cw h') (C.D.π h') := by
          rw [← X.cw_spec h, ← X.cw_spec h']
      _ = _ := X.emb_mul _ _ _ _
  have := X.cw_emb (X.cw h + vact (C.D.π h) (X.cw h')) (C.D.π h * C.D.π h')
  rw [← e3] at this
  exact this

theorem cw4_mul (h h' : ↥H) (hh : C.D.π h 4 = 4) :
    (X.cw (h * h')).1 4 = (X.cw h).1 4 + (X.cw h').1 4 := by
  rw [X.cw_mul]
  show (X.cw h).1 4 + pact (C.D.π h) (X.cw h').1 4 = _
  rw [pact_four hh]

theorem cw4_one : (X.cw 1).1 4 = 0 := by
  have : (1 : ↥H) = X.emb 0 1 := X.emb_zero_one.symm
  rw [this, X.cw_emb]
  rfl

theorem cw4_pow (h : ↥H) (hh : C.D.π h 4 = 4) (n : ℕ) :
    (X.cw (h ^ n)).1 4 = n • (X.cw h).1 4 := by
  induction n with
  | zero => simpa using X.cw4_one
  | succ n ih =>
    have hpow : C.D.π (h ^ n) 4 = 4 := by
      rw [map_pow]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hh n
    rw [pow_succ, X.cw4_mul _ _ hpow, ih, succ_nsmul]

@[expose] def Ksub : Subgroup G where
  carrier := {x | ∃ (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)),
    σ ∈ A4std ∧ w.1 4 = 0 ∧ x = ((X.emb w σ : ↥H) : G)}
  mul_mem' := by
    rintro _ _ ⟨w, σ, hσ, hw, rfl⟩ ⟨w', σ', hσ', hw', rfl⟩
    have h4 : σ 4 = 4 := ((mem_A4set σ).mp hσ).1
    refine ⟨w + vact σ w', σ * σ', mul_mem hσ hσ', ?_, ?_⟩
    · show w.1 4 + pact σ w'.1 4 = 0
      rw [pact_four h4, hw, hw', add_zero]
    · exact congrArg Subtype.val (X.emb_mul w w' σ σ')
  one_mem' := ⟨0, 1, one_mem _, rfl, congrArg Subtype.val X.emb_zero_one.symm⟩
  inv_mem' := by
    rintro _ ⟨w, σ, hσ, hw, rfl⟩
    have h4 : σ 4 = 4 := ((mem_A4set σ).mp hσ).1
    refine ⟨vact σ⁻¹ w, σ⁻¹, inv_mem hσ, ?_, ?_⟩
    · show pact σ⁻¹ w.1 4 = 0
      have : σ⁻¹ 4 = 4 := Equiv.Perm.inv_eq_iff_eq.mpr h4.symm
      rw [pact_four this, hw]
    · exact congrArg Subtype.val (X.emb_inv w σ)

theorem s_mem_K {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ A4std) :
    ((X.s σ : ↥H) : G) ∈ borelK M L := by
  have hσ' := (mem_A4set σ).mp hσ
  obtain ⟨τ₁, h1, τ₂, h2, e1, e2, rfl⟩ := A4_gen3 σ ((mem_A4set σ).mpr hσ')
  have hone : ∀ τ ∈ A4set, τ ^ 3 = 1 → ((X.s τ : ↥H) : G) ∈ borelK M L := by
    intro τ hτ hτ3
    have hτ' := (mem_A4set τ).mp hτ
    have hML : ((X.s τ : ↥H) : G) ∈ M ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [C.mem_M_iff, X.hs]
        exact (mem_S4std τ).mpr hτ'.1
      · rw [X.mem_L_iff, X.hs]
        exact Equiv.Perm.mem_alternatingGroup.mpr hτ'.2
    have hcube : ((X.s τ : ↥H) : G) ^ 3 = 1 := by
      have : (X.s τ) ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
      have := congrArg Subtype.val this
      simpa using this
    have hdvd : orderOf ((X.s τ : ↥H) : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
    have hcop : (orderOf ((X.s τ : ↥H) : G)).Coprime 2 :=
      Nat.Coprime.coprime_dvd_left hdvd (by decide)
    exact mem_K_of_odd hML hcop
  have : X.s (τ₁ * τ₂) = X.s τ₁ * X.s τ₂ := map_mul _ _ _
  rw [this]
  exact mul_mem (hone τ₁ h1 e1) (hone τ₂ h2 e2)

theorem iV_comm_mem {a : Equiv.Perm (Fin 5)} (ha : a ∈ A4std) (w : evenWeight 5) :
    ((C.iV (w + vact a w) : ↥H) : G) ∈ borelK M L := by
  have hu : ((C.iV w : ↥H) : G) ∈ M ⊓ L := C.U_le_ML (C.iV_mem_U w)
  have hk := X.s_mem_K ha
  have h1 := K_conj hu hk
  have h2 : ((C.iV w : ↥H) : G) * ((X.s a : ↥H) : G) * ((C.iV w : ↥H) : G)⁻¹ *
      ((X.s a : ↥H) : G)⁻¹ ∈ borelK M L := mul_mem h1 (inv_mem hk)
  have hconj := C.conj_iV X.hTC (X.s a) w
  rw [X.hs] at hconj
  have hinv : (C.iV w)⁻¹ = C.iV w := inv_eq_of_mul_eq_one_right (C.iV_self w)
  have key : C.iV w * X.s a * (C.iV w)⁻¹ * (X.s a)⁻¹ = C.iV (w + vact a w) := by
    calc C.iV w * X.s a * (C.iV w)⁻¹ * (X.s a)⁻¹
        = C.iV w * (X.s a * C.iV w * (X.s a)⁻¹) := by rw [hinv]; group
      _ = C.iV w * C.iV (vact a w) := by rw [hconj]
      _ = C.iV (w + vact a w) := by rw [C.iV_add]
  have := congrArg Subtype.val key
  rw [← this]
  exact h2

theorem iV_mem_K {e : evenWeight 5} (he : e.1 4 = 0) : ((C.iV e : ↥H) : G) ∈ borelK M L := by
  have hg : ∀ (j : Fin 5) (g : evenWeight 5), j ∈ ({1, 2, 3} : Finset (Fin 5)) →
      g.1 = (Pi.single 0 1 : Fin 5 → ZMod 2) + Pi.single j 1 →
      ((C.iV g : ↥H) : G) ∈ borelK M L := by
    intro j g hj hgj
    obtain ⟨c, hc, hc0⟩ := exists_c3 j hj
    have hw0 : isEven w04 := w04_even
    have h := w04_comm c hc j hc0
    have : g = (⟨w04, hw0⟩ : evenWeight 5) + vact c ⟨w04, hw0⟩ := Subtype.ext (by
      rw [hgj, ← h]; rfl)
    rw [this]
    exact X.iV_comm_mem ((mem_A4std c).mpr hc) _
  let g1w : evenWeight 5 := ⟨g1, g1_even⟩
  let g2w : evenWeight 5 := ⟨g2, g2_even⟩
  let g3w : evenWeight 5 := ⟨g3, g3_even⟩
  have h1 : ((C.iV g1w : ↥H) : G) ∈ borelK M L :=
    hg 1 g1w (by decide) g1_eq.symm
  have h2 : ((C.iV g2w : ↥H) : G) ∈ borelK M L :=
    hg 2 g2w (by decide) g2_eq.symm
  have h3 : ((C.iV g3w : ↥H) : G) ∈ borelK M L :=
    hg 3 g3w (by decide) g3_eq.symm
  have hpick : ∀ (c : ZMod 2) (g : evenWeight 5), ((C.iV g : ↥H) : G) ∈ borelK M L →
      ((C.iV (if c = 1 then g else 0) : ↥H) : G) ∈ borelK M L := by
    intro c g hgK
    split_ifs
    · exact hgK
    · rw [C.iV_zero]
      exact one_mem _
  have hdecomp : e = (if e.1 1 = 1 then g1w else 0) + (if e.1 2 = 1 then g2w else 0) +
      (if e.1 3 = 1 then g3w else 0) := by
    apply Subtype.ext
    have := E8_gen e.1 ⟨e.2, he⟩
    conv_lhs => rw [this]
    simp only [AddSubgroup.coe_add]
    congr 2 <;> split_ifs <;> rfl
  rw [hdecomp, C.iV_add, C.iV_add]
  exact mul_mem (mul_mem (hpick _ _ h1) (hpick _ _ h2)) (hpick _ _ h3)

theorem Ksub_le_K : X.Ksub ≤ borelK M L := by
  rintro _ ⟨w, σ, hσ, hw, rfl⟩
  have : ((X.emb w σ : ↥H) : G) = ((C.iV w : ↥H) : G) * ((X.s σ : ↥H) : G) := rfl
  rw [this]
  exact mul_mem (X.iV_mem_K hw) (X.s_mem_K hσ)

theorem K_le_Ksub : borelK M L ≤ X.Ksub := by
  rw [borelK, pResidualOf_eq_opResidual, opResidual, Subgroup.closure_le]
  rintro x ⟨hxML, hcop⟩
  have hxH : x ∈ H := C56.le_H C.hcs hxML.2
  set h : ↥H := ⟨x, hxH⟩ with hh
  have hM : C.D.π h ∈ S4std := (C.mem_M_iff h).mp hxML.1
  have hL : C.D.π h ∈ alternatingGroup (Fin 5) := (X.mem_L_iff h).mp hxML.2
  have h4 : C.D.π h 4 = 4 := (mem_S4std _).mp hM
  have hA : C.D.π h ∈ A4std :=
    (mem_A4std _).mpr ((mem_A4set _).mpr ⟨h4, Equiv.Perm.mem_alternatingGroup.mp hL⟩)
  have hodd : Odd (orderOf x) := by
    have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop.symm
    exact Nat.odd_iff.mpr (by omega)
  have hpow : h ^ orderOf x = 1 := by
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one x)
  have hc4 : (X.cw h).1 4 = 0 := by
    have h1 := X.cw4_pow h h4 (orderOf x)
    rw [hpow, X.cw4_one, odd_nsmul_zmod2 hodd] at h1
    exact h1.symm
  exact ⟨X.cw h, C.D.π h, hA, hc4, congrArg Subtype.val (X.cw_spec h)⟩

theorem borelK_eq : borelK M L = X.Ksub := le_antisymm X.K_le_Ksub X.Ksub_le_K

end Sec

end CFSG.QuasithinUnique.A5
