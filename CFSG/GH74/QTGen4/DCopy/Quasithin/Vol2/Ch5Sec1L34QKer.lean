module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34QKer
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Thm4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem H_le_normalizer_Z₁_F4 (h5114 : Stmt5_1_14_first_F4) :
    H ≤ Subgroup.normalizer (Z₁ : Set G) :=
  (s.H_le_centralizer_F4 h5114).trans (Subgroup.centralizer_le_normalizer _)

theorem not_le_centralizer_V₂_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    ¬ oTwoUpper H ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  intro hKC
  apply s.not_le
  have hHN : H ≤ Subgroup.normalizer (conjClosure Z₁ D₃ : Set G) := by
    rw [s.hyp.H_eq_sup]
    exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _)) (s.T_le_normalizer_V₂ hF)
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hV₂ne : conjClosure Z₁ D₃ ≠ ⊥ := fun hb' => hz1 (by
    have := (le_conjClosure Z₁ D₃) hz
    rw [hb'] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (conjClosure Z₁ D₃ : Set G)) :=
    ⟨conjClosure Z₁ D₃, hV₂ne, isPGroup_of_isElemAbelian s.isElemAbelian_V₂, rfl⟩
  obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := (s.hyp.isUniqueM_F4 h5114).2 M' ⟨hM', hHN.trans hle'⟩
  exact (le_normalizer_conjClosure Z₁ D₃).trans (hM'eq ▸ hle')

theorem not_tildeOf_K_le_centralizer_F4 (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) : Set (SecQuot
        (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  intro hKC
  apply s.not_le_centralizer_V₂_F4 h5114 hF
  have hHN := s.H_le_normalizer_Z₁_F4 h5114
  have hHC := s.H_le_centralizer_F4 h5114
  obtain ⟨z, hz, hz1⟩ := s.exists_z
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.mp (s.Z₁_le_Z hz)).2.2
  have hV₂H : conjClosure Z₁ D₃ ≤ conjClosure (conjClosure Z₁ D₃) H := le_conjClosure _ H
  have hV₂N : conjClosure Z₁ D₃ ≤ Subgroup.normalizer (Z₁ : Set G) :=
    (s.V₂_le_T.trans s.hyp.hyp.hStar.1.1).trans hHN
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyH, hyo⟩
  have hyK : y ∈ oTwoUpper H := mem_oTwoUpper_of_odd hyH hyo
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro v hv

  have hc : y * v * y⁻¹ * v⁻¹ ∈ Z₁ := by
    have h1 := Subgroup.mem_centralizer_iff.mp
      (hKC (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨y, hHN hyH⟩) hyK)) _
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁) (x := ⟨v, hV₂N hv⟩)
        (hV₂H hv))
    have := commutator_mem_of_secMk_commute h1.symm
    simpa using this
  have hyz : y * z = z * y := (Subgroup.mem_centralizer_iff.mp (hHC hyH) z hz).symm
  rcases s.eq_one_or_eq hz hz1 hc with h1 | h1
  · have : y * v * y⁻¹ = v := by
      have := congrArg (· * v) h1
      simpa using this
    have e : y * v = v * y := by
      have := congrArg (· * y) this
      simpa [mul_assoc] using this
    exact e.symm
  · exfalso
    have e : y * v * y⁻¹ = z * v := by
      rw [← h1]; group
    exact conj_ne_mul_of_odd hyz hz2 hz1 hyo e

theorem tildeOf_pCoreOf_le_centralizer_F4 (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    tildeOf Z₁ (pCoreOf 2 H) ≤ Subgroup.centralizer
      (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H) : Set (SecQuot
        (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  have h21 := (h521 G T M L V H B D D₃ Z₁ H n s.hyp.hyp s.hyp.notation59 s.hyp.module
    s.hyp.l34 hnot s.le_D s.card_D₃ s.z1 le_rfl (s.H_le_centralizer_F4 h5114)).1
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
  have hc : (u : G) * x * (u : G)⁻¹ * (x : G)⁻¹ ∈ Z₁ :=
    h21 (Subgroup.commutator_mem_commutator hu hx)
  have h1 : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (u * x * u⁻¹ * x⁻¹) = 1 := by
    rw [secMk_eq_one_iff]; simpa using hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ x) h1
  simp only [one_mul, inv_mul_cancel_right] at this
  have := congrArg (· * secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ u) this
  simpa [mul_assoc] using this

end Setup521

namespace Setup521

variable {D₃ Z₁ : Subgroup G} (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

section Section

variable {W : Subgroup (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)}

theorem tildeCent_le_pCoreOf_F4
    (h5114 : Stmt5_1_14_first_F4)
    (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    tildeCent Z₁ H W ≤ pCoreOf 2 H := by
  have hHN := s.H_le_normalizer_Z₁_F4 h5114
  have hnorm : H ≤ Subgroup.normalizer (tildeCent Z₁ H W : Set G) := by
    intro h hh
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hxH : x ∈ H := hx.1
    have hy : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    refine (mem_tildeCent_iff (hHN hy)).mpr ⟨hy, ?_⟩
    have hx' := ((mem_tildeCent_iff (hHN hxH)).mp hx).2
    have hπh := le_normalizer_centralizer_of_le_normalizer hW
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨h, hHN hh⟩) hh)
    have h1 := (Subgroup.mem_normalizer_iff.mp hπh _).mp hx'
    have e : (⟨h * x * h⁻¹, hHN hy⟩ : ↥(Subgroup.normalizer (Z₁ : Set G))) =
        ⟨h, hHN hh⟩ * ⟨x, hHN hxH⟩ * ⟨h, hHN hh⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact h1
  refine s.hyp.le_pCoreOf_of_not_le inf_le_left hnorm fun hK => hKW ?_
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  exact ((mem_tildeCent_iff x.2).mp (hK hx)).2

theorem mem_pCoreOf_of_mem_centralizer_F4
    (h5114 : Stmt5_1_14_first_F4)
    (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
    {h : G} (hh : h ∈ H) (hN : h ∈ Subgroup.normalizer (Z₁ : Set G))
    (hc : tmk Z₁ ⟨h, hN⟩ ∈
      Subgroup.centralizer (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) :
    h ∈ pCoreOf 2 H :=
  s.tildeCent_le_pCoreOf_F4 h5114 hW hKW ((mem_tildeCent_iff hN).mpr ⟨hh, hc⟩)

variable (hWU : W ≤ tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H))
  (hW : tildeOf Z₁ H ≤ Subgroup.normalizer
    (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
  (hKW : ¬ tildeOf Z₁ (oTwoUpper H) ≤ Subgroup.centralizer
    (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁)))
include hWU hW hKW

theorem ker_tildeAct_K_F4
    (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    (tildeAct Z₁ (oTwoUpper H) ((oTwoUpper_le H).trans (s.H_le_normalizer_Z₁_F4 h5114)) W
      ((tildeOf_mono (oTwoUpper_le H)).trans hW)).ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext k
  rw [mem_ker_tildeAct]
  constructor
  · intro hc
    have h2 := s.mem_pCoreOf_of_mem_centralizer_F4 h5114 hW hKW (oTwoUpper_le H k.2) _ hc
    obtain ⟨k', hk', hk'k⟩ := inf_pCoreOf_oTwoUpper_le H ⟨h2, k.2⟩
    have : k' = k := Subtype.ext hk'k
    rw [← this]
    exact hk'
  · intro hk
    have h1 : (k : G) ∈ pCoreOf 2 (oTwoUpper H) := ⟨k, by assumption, rfl⟩
    have h2 := s.tildeOf_pCoreOf_le_centralizer_F4 h5114 h521 hnot
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨k, s.H_le_normalizer_Z₁_F4 h5114 (oTwoUpper_le H k.2)⟩) (pCoreOf_K_le h1))
    exact Subgroup.centralizer_le hWU h2

theorem lieModel_autOn_F4
    (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    LieModel ↥(autOn (tildeOf Z₁ (oTwoUpper H)) W) .PSL 3 2 2 := by
  have hker := s.ker_tildeAct_K_F4 hWU hW hKW h5114 h521 hnot
  let e : O2Q (oTwoUpper H) ≃* ↥(autOn (tildeOf Z₁ (oTwoUpper H)) W) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (tildeAct_surjective _ _))
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e s.hyp.l34

theorem isPGroup_inf_centralizer_F4
    (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    IsPGroup 2 ↥(tildeOf Z₁ (oTwoUpper H) ⊓ Subgroup.centralizer
      (W : Set (SecQuot (Subgroup.normalizer (Z₁ : Set G)) Z₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := s.ker_tildeAct_K_F4 hWU hW hKW h5114 h521 hnot
  rintro ⟨x, hxK, hxC⟩
  obtain ⟨k, hk, rfl⟩ := mem_secImg.mp hxK
  have hk' : (⟨k, hk⟩ : ↥(oTwoUpper H)) ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
    rw [← hker, mem_ker_tildeAct]
    exact hxC
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, hk'⟩
  have ha' : (k : G) ^ 2 ^ a = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥(oTwoUpper H)) => ((y : ↥(oTwoUpper H)) : G)) ha
    simpa using this
  have hka : k ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha')
  refine ⟨a, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← map_pow, hka, map_one]

theorem pCoreOf_autOn_eq_bot_F4
    (h5114 : Stmt5_1_14_first_F4) (h521 : Stmt5_1_21_F4)
    (hnot : ¬ Concl5_1_14_four T L V B D n) :
    pCoreOf 2 (autOn (tildeOf Z₁ H) W) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN := s.H_le_normalizer_Z₁_F4 h5114
  set ρ := tildeAct Z₁ H hHN W hW with hρ
  have hsurj : Function.Surjective ρ := tildeAct_surjective _ _
  have hkerρ : ∀ x : ↥H, x ∈ ρ.ker → (x : G) ∈ pCoreOf 2 H := fun x hx =>
    s.mem_pCoreOf_of_mem_centralizer_F4 h5114 hW hKW x.2 _ ((mem_ker_tildeAct _ _ x).mp hx)
  have hρO : ∀ y : ↥H, (y : G) ∈ pCoreOf 2 H → ρ y = 1 := by
    intro y hy
    rw [← MonoidHom.mem_ker, mem_ker_tildeAct]
    exact Subgroup.centralizer_le hWU (s.tildeOf_pCoreOf_le_centralizer_F4 h5114 h521 hnot
      (secMk_mem_secImg (A := Subgroup.normalizer (Z₁ : Set G)) (B := Z₁)
        (x := ⟨y, hHN y.2⟩) hy))
  set Q := CFSG.Open.pCore 2 ↥(autOn (tildeOf Z₁ H) W) with hQ
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCore_isPGroup 2

  have hPre2 : IsPGroup 2 ↥((Q.comap ρ).map H.subtype) := by
    rintro ⟨x, ⟨y, hy, rfl⟩⟩
    obtain ⟨a, ha⟩ := hQp ⟨ρ y, Subgroup.mem_comap.mp hy⟩
    have h1 : ρ (y ^ 2 ^ a) = 1 := by
      rw [map_pow]; simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hkerρ _ h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((y : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.subtype_apply]
    rw [pow_add, pow_mul, hb']
  have hPreN : H ≤ Subgroup.normalizer (((Q.comap ρ).map H.subtype : Subgroup G) : Set G) := by
    intro h hh
    apply mem_normalizer_of_forall_conj_mem'
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hQn.conj_mem _ (Subgroup.mem_comap.mp hy) _
  have hPreO : (Q.comap ρ).map H.subtype ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hPreN hPre2
  have hQbot : Q = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := hsurj q
    rw [Subgroup.mem_bot]
    exact hρO y (hPreO ⟨y, Subgroup.mem_comap.mpr hq, rfl⟩)
  show Q.map (autOn (tildeOf Z₁ H) W).subtype = ⊥
  rw [hQbot, Subgroup.map_bot]

end Section

end Setup521

end CFSG.Quasithin.H13
