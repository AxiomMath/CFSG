module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdStep2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37A1

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem conjR_conjR_inv (X : Subgroup G) (g : G) : conjR (conjR X g⁻¹) g = X := by
  have h := BenderBranch.conjugate_conjugate X g⁻¹ g
  rw [inv_mul_cancel, BenderBranch.conjugate_one] at h
  exact h

theorem conjR_conjR_eq (X : Subgroup G) (g h : G) : conjR (conjR X g) h = conjR X (g * h) :=
  BenderBranch.conjugate_conjugate X g h

theorem card_conjR (X : Subgroup G) (g : G) : Nat.card ↥(conjR X g) = Nat.card ↥X :=
  BenderBranch.card_conjugate X g

theorem mem_normalizer_iff_conjR_eq {X : Subgroup G} {g : G} :
    g ∈ normalizer (X : Set G) ↔ conjR X g = X :=
  BenderBranch.conjugate_eq_iff_mem_normalizer.symm

theorem map_conj_centralizerElem {i j : G} (g : G) (hij : g⁻¹ * i * g = j) :
    (centralizerElem i).map (MulAut.conj g⁻¹).toMonoidHom = centralizerElem j := by
  ext y
  rw [Subgroup.mem_map_equiv]
  rw [MulAut.conj_symm_apply, inv_inv]
  unfold centralizerElem
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hij]
  constructor
  · intro h
    calc y * (g⁻¹ * i * g) = g⁻¹ * ((g * y * g⁻¹) * i) * g := by group
      _ = g⁻¹ * (i * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * i * g) * y := by group
  · intro h
    calc (g * y * g⁻¹) * i = g * (y * (g⁻¹ * i * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * i * g) * y) * g⁻¹ := by rw [h]
      _ = i * (g * y * g⁻¹) := by group

theorem isComponentIn_conj_cent {A : Subgroup G} {i j : G} (g : G) (hij : g⁻¹ * i * g = j)
    (h : IsComponentIn A (centralizerElem i)) : IsComponentIn (conjR A g) (centralizerElem j) := by
  have h1 := BenderBranch.isComponentIn_map (MulAut.conj g⁻¹) h
  rw [map_conj_centralizerElem g hij] at h1
  exact h1

@[expose] def UniqComp (J : Subgroup G) (w : G) : Prop :=
  ∀ J' : Subgroup G, IsComponentIn J' (centralizerElem w) ↔ J' = J

theorem UniqComp.isComponentIn {J : Subgroup G} {w : G} (h : UniqComp J w) :
    IsComponentIn J (centralizerElem w) := (h J).mpr rfl

theorem UniqComp.eq {J J' : Subgroup G} {w : G} (h : UniqComp J w) (h' : UniqComp J' w) :
    J = J' := ((h' J).mp h.isComponentIn)

theorem UniqComp.conj {J : Subgroup G} {w : G} (h : UniqComp J w) (g : G) :
    UniqComp (conjR J g) (g⁻¹ * w * g) := by
  intro J'
  constructor
  · intro hJ'
    have h1 : IsComponentIn (conjR J' g⁻¹) (centralizerElem w) :=
      isComponentIn_conj_cent g⁻¹ (by group) hJ'
    have h2 : conjR J' g⁻¹ = J := (h _).mp h1
    rw [← h2, conjR_conjR_inv]
  · rintro rfl
    exact isComponentIn_conj_cent g rfl h.isComponentIn

theorem UniqComp.mem_normalizer_of_commute {J : Subgroup G} {w g : G} (h : UniqComp J w)
    (hg : g * w = w * g) : g ∈ normalizer (J : Set G) := by
  have h1 := h.conj g
  have e : g⁻¹ * w * g = w := by
    calc g⁻¹ * w * g = g⁻¹ * (w * g) := by group
      _ = g⁻¹ * (g * w) := by rw [← hg]
      _ = w := by group
  rw [e] at h1
  exact mem_normalizer_iff_conjR_eq.mpr (h.eq h1).symm

theorem UniqComp.mem_normalizer {J : Subgroup G} {w g : G} (h : UniqComp J w)
    (h' : UniqComp J (g⁻¹ * w * g)) : g ∈ normalizer (J : Set G) :=
  mem_normalizer_iff_conjR_eq.mpr (h'.eq (h.conj g)).symm

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.uniqComp_z₂ (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : UniqComp K z₂ := by
  intro J
  constructor
  · intro hJ
    have hlay := (lemma2_4_33 hD h27_1 G T M H S L s x z₁ z₂ K hK).1
    have hJK : J ≤ K := by
      rw [← hlay]
      exact le_sSup hJ
    exact Id2519.eq_of_isComponentIn_of_isQuasisimple
      (BenderBranch.isComponentIn_of_le hJ hJK hK.K_comp.1)
      (BenderBranch.isQuasisimple_of_isComponentIn hK.K_comp)
  · rintro rfl
    exact hK.K_comp

theorem A3A3K.isSimpleGroup
    (hK : A3A3K T M H S L s x z₁ z₂ K) : IsSimpleGroup ↥K := by
  rcases hK.K_iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  · have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hd : L2pData PSL(2, ZMod 7) :=
      Unc25K1.psl2_l2pData (K := ZMod 7) (p := 7) le_rfl (by simp)
        (Or.inr ⟨by norm_num, 3, by norm_num⟩)
    exact (MulEquiv.isSimpleGroup_congr e).mpr hd.simple

theorem A3A3K.card_cases (hK : A3A3K T M H S L s x z₁ z₂ K) :
    Nat.card K = 168 ∨ Nat.card K = 360 := by
  rcases hK.K_iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · right
    exact (Nat.card_congr e.toEquiv).trans card_alt6'
  · left
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hF : ringChar (ZMod 7) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]; norm_num
    have h5 : 5 ≤ Fintype.card (ZMod 7) := by simp
    have h := CFSG.QuasithinUnique.K1.psl2_card_mul_two hF h5
    simp only [ZMod.card] at h
    have h' : Nat.card PSL(2, ZMod 7) * 2 = 336 := h.trans (by norm_num)
    rw [Nat.card_congr e.toEquiv]
    omega

theorem A3A3K.nonabelian (hK : A3A3K T M H S L s x z₁ z₂ K) : ∃ a b : ↥K, a * b ≠ b * a := by
  obtain ⟨c, hcL, -, hcN, hcfp, -⟩ := hK.isA4.exists_c
  have hnt : Nontrivial ↥(blockU L) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hK.isA4.card_U]; norm_num)
  obtain ⟨u, hu1⟩ := exists_ne (1 : ↥(blockU L))
  have huU : (u : G) ∈ blockU L := u.2
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine ⟨⟨c, hK.L_le_K hcL⟩, ⟨u, hK.L_le_K (hK.isA4.le huU)⟩, fun h => ?_⟩
  have h' : c * (u : G) = (u : G) * c := congrArg Subtype.val h
  apply hcfp _ huU hu1'
  calc c * (u : G) * c⁻¹ = (u : G) * c * c⁻¹ := by rw [h']
    _ = u := by group

theorem A3A3K.mem_blockU2_of_mem (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) {v : G} (hv : v ∈ blockU L) :
    s * v * s⁻¹ ∈ blockU2 L s := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hss : s * s ∈ baum S := (s_mul_self_mem_baum hB hK.toA3A3).2
  have hUn := baum_le_normalizer_blockU hK.cs hK.a3
  rw [blockU2, mem_conjR]
  have e : s * (s * v * s⁻¹) * s⁻¹ = (s * s) * v * (s * s)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hUn hss) v).mp hv

section Comp

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))
include hD h27_1 hI hK hc

theorem A3A3K.conjR_eq_of_mem {g : G} (hg : g ∈ conjR L s) : conjR K g = K := by
  have hAs : IsA4Block (conjR L s) (blockU2 L s) := hK.isA4s
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hz₂1 : z₂ ≠ 1 := hK.toA3A3x.z₂_ne
  have hz₂sq : z₂ ^ 2 = 1 := hK.toA3A3x.sq₂
  have huU : g⁻¹ * z₂ * g ∈ blockU2 L s := by
    have := (Subgroup.mem_normalizer_iff.mp (hAs.le_normalizer ((conjR L s).inv_mem hg)) z₂).mp
      hz₂U
    simpa using this
  have hu1 : g⁻¹ * z₂ * g ≠ 1 := by
    intro h
    apply hz₂1
    calc z₂ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hu2 : (g⁻¹ * z₂ * g) ^ 2 = 1 := hAs.sq_U _ huU
  have huv : (g⁻¹ * z₂ * g) * z₂ = z₂ * (g⁻¹ * z₂ * g) := hAs.comm_U _ huU z₂ hz₂U
  have hKu : K ≤ centralizerElem (g⁻¹ * z₂ * g) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hc huU) k hk)
  have hKz : K ≤ centralizerElem z₂ := hK.K_comp.1
  have hX : IsComponentIn K (Subgroup.centralizer ({g⁻¹ * z₂ * g} : Set G) ⊓
      Subgroup.centralizer ({z₂} : Set G)) :=
    BenderBranch.isComponentIn_of_le hK.K_comp (le_inf hKu hKz) inf_le_right
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hXe : 2 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le hUK
    rw [hK.isA4.card_U] at this
    exact (by norm_num : 2 ∣ 4).trans this
  have hX4 : ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 :=
    ⟨blockU L, hUK, hK.isA4.isElemAbelian_U, hK.isA4.card_U⟩
  obtain ⟨hXY, hcases⟩ := Id2519.step2 hI.i32 hI.p121_3 hI.p121_5 hK.cs.setting.simple
    hK.cs.setting.nonabelian hK.cs.setting.qtke hu1 hu2 hz₂1 hz₂sq huv hX hXe hX4
  have hU : UniqComp (conjR K g) (g⁻¹ * z₂ * g) := (hK.uniqComp_z₂ hD h27_1).conj g
  have hz₂C : z₂ ∈ centralizerElem (g⁻¹ * z₂ * g) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huv.symm
  rcases hcases with ⟨J, hJ, hYJ, -⟩ | ⟨J, hJ, hJne, -⟩
  · have hKJ : K ≤ J := hYJ ▸ hXY
    have hJeq : J = conjR K g := (hU J).mp hJ
    rw [hJeq] at hKJ
    exact (Subgroup.eq_of_le_of_card_ge hKJ (card_conjR K g).le).symm
  · exfalso
    have e1 : J = conjR K g := (hU J).mp hJ
    have hJ' := Unc25G2.isComponentIn_conjugate hJ hz₂C
    have e2 : CFSG.conjugate J z₂ = conjR K g := (hU _).mp hJ'
    exact hJne (e1.trans e2.symm)

theorem A3A3K.uniqComp_of_mem_U₂ {v : G} (hv : v ∈ blockU2 L s) (hv1 : v ≠ 1) : UniqComp K v := by
  have hAs : IsA4Block (conjR L s) (blockU2 L s) := hK.isA4s
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  obtain ⟨g, hg, hvg⟩ := hAs.exists_conj hz₂U hv hK.toA3A3x.z₂_ne hv1
  have h := (hK.uniqComp_z₂ hD h27_1).conj g
  rw [hK.conjR_eq_of_mem hD h27_1 hI hc hg] at h
  rw [hvg]
  exact h

theorem A3A3K.uniqComp_of_mem_U {v : G} (hv : v ∈ blockU L) (hv1 : v ≠ 1) :
    UniqComp (conjR K s) v := by
  have hu : s * v * s⁻¹ ∈ blockU2 L s := hK.mem_blockU2_of_mem hD h27_1 hv
  have hu1 : s * v * s⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = s⁻¹ * (s * v * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  have h := (hK.uniqComp_of_mem_U₂ hD h27_1 hI hc hu hu1).conj s
  have e : s⁻¹ * (s * v * s⁻¹) * s = v := by group
  rw [e] at h
  exact h

theorem A3A3K.x_mem_normalizer_Ks : x ∈ normalizer ((conjR K s : Subgroup G) : Set G) :=
  (hK.uniqComp_of_mem_U hD h27_1 hI hc hK.toA3A3x.z₁_mem.1 hK.z₁_ne).mem_normalizer_of_commute
    hK.x_comm₁

theorem A3A3K.uniqComp_of_mem_Ux {w : G} (hw : w ∈ conjR (blockU L) x) (hw1 : w ≠ 1) :
    UniqComp (conjR K s) w := by
  have hv : x * w * x⁻¹ ∈ blockU L := mem_conjR.mp hw
  have hv1 : x * w * x⁻¹ ≠ 1 := by
    intro h
    apply hw1
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have h := (hK.uniqComp_of_mem_U hD h27_1 hI hc hv hv1).conj x
  have e : x⁻¹ * (x * w * x⁻¹) * x = w := by group
  rw [e, mem_normalizer_iff_conjR_eq.mp (hK.x_mem_normalizer_Ks hD h27_1 hI hc)] at h
  exact h

theorem A3A3K.normalizer_blockU_le : normalizer (blockU L : Set G) ≤
    normalizer ((conjR K s : Subgroup G) : Set G) := by
  intro g hg
  have hz₁U : z₁ ∈ blockU L := hK.toA3A3x.z₁_mem.1
  have hz₁1 : z₁ ≠ 1 := hK.z₁_ne
  have hv : g⁻¹ * z₁ * g ∈ blockU L := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (blockU L : Set G)).inv_mem hg) z₁).mp hz₁U
    simpa using this
  have hv1 : g⁻¹ * z₁ * g ≠ 1 := by
    intro h
    apply hz₁1
    calc z₁ = g * (g⁻¹ * z₁ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  exact (hK.uniqComp_of_mem_U hD h27_1 hI hc hz₁U hz₁1).mem_normalizer
    (hK.uniqComp_of_mem_U hD h27_1 hI hc hv hv1)

theorem A3A3K.normalizer_blockUx_le : normalizer (conjR (blockU L) x : Set G) ≤
    normalizer ((conjR K s : Subgroup G) : Set G) := by
  intro g hg
  have hz₁U : z₁ ∈ conjR (blockU L) x := by
    rw [mem_conjR]
    have : x * z₁ * x⁻¹ = z₁ := by
      calc x * z₁ * x⁻¹ = z₁ * x * x⁻¹ := by rw [hK.x_comm₁]
        _ = z₁ := by group
    rw [this]
    exact hK.toA3A3x.z₁_mem.1
  have hz₁1 : z₁ ≠ 1 := hK.z₁_ne
  have hv : g⁻¹ * z₁ * g ∈ conjR (blockU L) x := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((normalizer (conjR (blockU L) x : Set G)).inv_mem hg) z₁).mp hz₁U
    simpa using this
  have hv1 : g⁻¹ * z₁ * g ≠ 1 := by
    intro h
    apply hz₁1
    calc z₁ = g * (g⁻¹ * z₁ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  exact (hK.uniqComp_of_mem_Ux hD h27_1 hI hc hz₁U hz₁1).mem_normalizer
    (hK.uniqComp_of_mem_Ux hD h27_1 hI hc hv hv1)

theorem A3A3K.K_le_normalizer_Ks
    : K ≤ normalizer ((conjR K s : Subgroup G) : Set G) := by
  have hcs := hK.cs
  have hxG₂ : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  have hxK : x ∈ normalizer (K : Set G) := hK.K_norm hxG₂
  have hLxK : conjR L x ≤ K := by
    have h1 : conjR L x ≤ conjR K x := by
      intro y hy
      rw [mem_conjR] at hy ⊢
      exact hK.L_le_K hy
    rwa [mem_normalizer_iff_conjR_eq.mp hxK] at h1
  have hUne : blockU L ≠ conjR (blockU L) x := by
    intro h
    apply hK.x_good
    rw [← h]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => hK.isA4.comm_U v hv u hu
  have hUx := hK.blockUx_le_rK hD h27_1
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hbT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have h2 : IsPGroup 2 ↥(blockU L ⊔ conjR (blockU L) x) := by
    have hle : blockU L ⊔ conjR (blockU L) x ≤ T :=
      sup_le (hUB.trans hbT) ((hUx.trans (inf_le_left : baum S ⊓ K ≤ baum S)).trans hbT)
    exact hcs.setting.isPGroup.to_le hle
  have hsup := sup_eq_of_two_A4 hK.isSimpleGroup hK.card_cases hK.isA4 (hK.isA4.conj x) hK.L_le_K
    hLxK hUne h2
  refine hsup.symm.le.trans (sup_le ?_ ?_)
  · exact hK.isA4.le_normalizer.trans (hK.normalizer_blockU_le hD h27_1 hI hc)
  · exact (hK.isA4.conj x).le_normalizer.trans (hK.normalizer_blockUx_le hD h27_1 hI hc)

omit hI in
theorem A3A3K.z₁_mem_centralizer_Ks : z₁ ∈ Subgroup.centralizer ((conjR K s : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro κ hκ
  have hκ' : s * κ * s⁻¹ ∈ K := mem_conjR.mp hκ
  have hu : s * z₁ * s⁻¹ ∈ blockU2 L s := hK.mem_blockU2_of_mem hD h27_1 hK.toA3A3x.z₁_mem.1
  have h1 : (s * κ * s⁻¹) * (s * z₁ * s⁻¹) = (s * z₁ * s⁻¹) * (s * κ * s⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hc hu) _ hκ'
  have : κ * z₁ = z₁ * κ := by
    have h2 : s⁻¹ * ((s * κ * s⁻¹) * (s * z₁ * s⁻¹)) * s =
        s⁻¹ * ((s * z₁ * s⁻¹) * (s * κ * s⁻¹)) * s := by rw [h1]
    calc κ * z₁ = s⁻¹ * ((s * κ * s⁻¹) * (s * z₁ * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * z₁ * s⁻¹) * (s * κ * s⁻¹)) * s := h2
      _ = z₁ * κ := by group
  exact this

theorem A3A3K.K_le_centralizer_Ks
    : K ≤ Subgroup.centralizer ((conjR K s : Subgroup G) : Set G) := by
  have hKN := hK.K_le_normalizer_Ks hD h27_1 hI hc
  have hz₁K : z₁ ∈ K := hK.z₁_mem_K
  let N₀ : Subgroup ↥K := (Subgroup.centralizer ((conjR K s : Subgroup G) : Set G)).subgroupOf K
  have hN₀ : N₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.centralizer ((conjR K s : Subgroup G) : Set G) := hn
    show ((g * n * g⁻¹ : ↥K) : G) ∈ Subgroup.centralizer ((conjR K s : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro κ hκ
    have hgN : (g : G) ∈ normalizer ((conjR K s : Subgroup G) : Set G) := hKN g.2
    have hκ' : (g : G)⁻¹ * κ * g ∈ conjR K s := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer ((conjR K s : Subgroup G) : Set G)).inv_mem
        hgN) κ).mp hκ
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hn' _ hκ'
    calc κ * ((g : G) * (n : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * κ * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * κ * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * κ := by group
  have hz₁N₀ : (⟨z₁, hz₁K⟩ : ↥K) ∈ N₀ := hK.z₁_mem_centralizer_Ks hD h27_1 hc
  have hsimple := hK.isSimpleGroup
  have htop : N₀ = ⊤ := by
    rcases (haveI := hN₀; hsimple.eq_bot_or_eq_top_of_normal N₀) with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at hz₁N₀
      exact hK.z₁_ne (congrArg Subtype.val hz₁N₀)
    · exact h
  intro a ha κ hκ
  have : (⟨a, ha⟩ : ↥K) ∈ N₀ := by rw [htop]; exact Subgroup.mem_top _
  have h3 : a ∈ Subgroup.centralizer ((conjR K s : Subgroup G) : Set G) := this
  exact Subgroup.mem_centralizer_iff.mp h3 κ hκ

end Comp

end Main

end CFSG.QuasithinUnique.DoubleA3
