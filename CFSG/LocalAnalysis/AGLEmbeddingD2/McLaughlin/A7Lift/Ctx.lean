module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Sylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbeddingD2.McLaughlin.A7Six Equiv Equiv.Perm
open scoped Pointwise

variable {X : Type} [Group X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

structure SevenCtx0 (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) where
  eL : ↥L ≃* alternatingGroup (Fin 7)
  θs : ↥(nLs T L) →* Perm (Fin 7)
  hθs : ∀ (y : ↥(nLs T L)) (l l' : ↥L), (l' : X ⧸ gnC T) = (y : X ⧸ gnC T) * l *
    (y : X ⧸ gnC T)⁻¹ → (eL l' : Perm (Fin 7)) = θs y * eL l * (θs y)⁻¹
  hθsL : ∀ (y : ↥(nLs T L)) (l : ↥L), (l : X ⧸ gnC T) = y → θs y = eL l
  hθs1 : ∀ y : ↥(nLs T L), θs y = 1 ↔ ∀ l ∈ L, (y : X ⧸ gnC T) * l * (y : X ⧸ gnC T)⁻¹ = l

theorem SevenCtx0.exists_eL (T : Subgroup X) (L : Subgroup (X ⧸ gnC T))
    (eL : ↥L ≃* alternatingGroup (Fin 7)) : ∃ c : SevenCtx0 T L, c.eL = eL := by
  obtain ⟨θ, h1, h2, h3⟩ := exists_thetaS T L eL
  exact ⟨⟨eL, θ, h1, h2, h3⟩, rfl⟩

@[expose] def _root_.CFSG.AGLEmbeddingD2.McLaughlin.A7Six.SixCtx.toSevenCtx0
    (c : SixCtx T L) : SevenCtx0 T L :=
  ⟨c.eL, c.θs, c.hθs, c.hθsL, c.hθs1⟩

@[expose] def SevenCtx0.θ (c : SevenCtx0 T L) : ↥(nL T L) →* Perm (Fin 7) :=
  c.θs.comp (πN T L)

abbrev SevenCtx0.img (c : SevenCtx0 T L) (A : Subgroup X) : Subgroup (Perm (Fin 7)) :=
  (A.subgroupOf (nL T L)).map c.θ

abbrev SevenCtx0.imgS (c : SevenCtx0 T L) (K : Subgroup (X ⧸ gnC T)) :
    Subgroup (Perm (Fin 7)) :=
  (K.subgroupOf (nLs T L)).map c.θs

@[expose] def SevenCtx0.wP (c : SevenCtx0 T L) (P : Subgroup (Perm (Fin 7))) :
    Subgroup (X ⧸ gnC T) :=
  (P.comap ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom)).map L.subtype

namespace SevenCtx0

variable (c : SevenCtx0 T L)

theorem mem_img {A : Subgroup X} (hA : A ≤ nL T L) {σ : Perm (Fin 7)} :
    σ ∈ c.img A ↔ ∃ (a : X) (ha : a ∈ A), c.θ ⟨a, hA ha⟩ = σ := by
  constructor
  · rintro ⟨⟨a, ha'⟩, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem mem_imgS {K : Subgroup (X ⧸ gnC T)} (hK : K ≤ nLs T L) {σ : Perm (Fin 7)} :
    σ ∈ c.imgS K ↔ ∃ (y : X ⧸ gnC T) (hy : y ∈ K), c.θs ⟨y, hK hy⟩ = σ := by
  constructor
  · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hK hy⟩, hy, rfl⟩

theorem imgS_map (R : Subgroup X) (hR : R ≤ nL T L) :
    c.imgS (R.map (QuotientGroup.mk' (gnC T))) = c.img R := by
  ext σ
  have hRs : R.map (QuotientGroup.mk' (gnC T)) ≤ nLs T L := by
    rintro _ ⟨r, hr, rfl⟩
    exact hR hr
  rw [c.mem_imgS hRs, c.mem_img hR]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩

theorem mem_wP {P : Subgroup (Perm (Fin 7))} {x : X ⧸ gnC T} :
    x ∈ c.wP P ↔ ∃ hx : x ∈ L, ((c.eL ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ P := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyP, rfl⟩
    exact ⟨hy, hyP⟩
  · rintro ⟨hx, hxP⟩
    exact ⟨⟨x, hx⟩, hxP, rfl⟩

theorem wP_le_L (P : Subgroup (Perm (Fin 7))) : c.wP P ≤ L := fun _ hx => ((c.mem_wP).1 hx).1

theorem θs_of_mem_L {y : ↥(nLs T L)} (hy : (y : X ⧸ gnC T) ∈ L) :
    c.θs y = c.eL ⟨y, hy⟩ :=
  c.hθsL y ⟨y, hy⟩ rfl

include c in
theorem eq_one_of_mem_center {z : X ⧸ gnC T} (hz : z ∈ L) (hc : ∀ l ∈ L, z * l = l * z) :
    z = 1 := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
      with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : alternatingGroup (Fin 7), a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      have h1 : (⟨swap 0 1 * swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ : alternatingGroup (Fin 7)) *
          ⟨swap 0 1 * swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ ≠
          ⟨swap 0 1 * swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ *
          ⟨swap 0 1 * swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ := by
        intro h
        have := congrArg Subtype.val h
        revert this
        decide
      exact h1 (hcomm _ _)
  have h1 : c.eL ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨l, rfl⟩ := c.eL.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc l l.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  have h2 : (⟨z, hz⟩ : ↥L) = 1 := c.eL.injective (h1.trans (map_one c.eL).symm)
  exact congrArg Subtype.val h2

theorem le_of_closure {K : Subgroup (X ⧸ gnC T)} {Sig : Set (Perm (Fin 7))}
    (hgen : alternatingGroup (Fin 7) ≤ Subgroup.closure Sig)
    (hSig : ∀ σ ∈ Sig, ∃ l : ↥L, (l : X ⧸ gnC T) ∈ K ∧ (c.eL l : Perm (Fin 7)) = σ) : L ≤ K := by
  set K₀ : Subgroup (Perm (Fin 7)) :=
    (K.comap L.subtype).map ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom)
  have hle : Subgroup.closure Sig ≤ K₀ := by
    refine (Subgroup.closure_le _).2 fun σ hσ => ?_
    obtain ⟨l, hlK, hl⟩ := hSig σ hσ
    exact ⟨l, hlK, hl⟩
  intro x hx
  have h1 : ((c.eL ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ K₀ :=
    hle (hgen (c.eL ⟨x, hx⟩).2)
  obtain ⟨k, hkK, hk⟩ := h1
  have h2 : c.eL k = c.eL ⟨x, hx⟩ := Subtype.ext hk
  have h3 := c.eL.injective h2
  have h4 : (k : X ⧸ gnC T) = x := congrArg Subtype.val h3
  rw [← h4]
  exact hkK

theorem mem_of_wP_le {K : Subgroup (X ⧸ gnC T)} {P : Subgroup (Perm (Fin 7))} (hW : c.wP P ≤ K)
    {σ : Perm (Fin 7)} (hσ : σ ∈ (P ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7)))) :
    ∃ l : ↥L, (l : X ⧸ gnC T) ∈ K ∧ (c.eL l : Perm (Fin 7)) = σ := by
  refine ⟨c.eL.symm ⟨σ, hσ.2⟩, hW ((c.mem_wP).2 ⟨(c.eL.symm ⟨σ, hσ.2⟩).2, ?_⟩), ?_⟩
  · rw [show (⟨((c.eL.symm ⟨σ, hσ.2⟩ : ↥L) : X ⧸ gnC T), (c.eL.symm ⟨σ, hσ.2⟩).2⟩ : ↥L) =
      c.eL.symm ⟨σ, hσ.2⟩ from rfl, MulEquiv.apply_symm_apply]
    exact hσ.1
  · rw [MulEquiv.apply_symm_apply]

section

variable [Finite X]

private theorem img_inf_lT_eq (c : SevenCtx0 T L) :
    c.img (T ⊓ lT T L) = ((gnImg T T ⊓ L).subgroupOf L).map
      ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom) := by
  classical
  set A : Subgroup X := T ⊓ lT T L with hA
  have hAnL : A ≤ nL T L := by
    intro a ha
    exact Subgroup.mem_comap.2 (Subgroup.le_normalizer ha.2)
  set K : Subgroup (X ⧸ gnC T) := gnImg T T ⊓ L with hK
  set e : ↥L →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom with he
  have hmA : ∀ (a : X), a ∈ T → QuotientGroup.mk' (gnC T) a ∈ L → a ∈ A := by
    intro a haT haL
    rw [hA]
    exact ⟨haT, Subgroup.mem_comap.2 haL⟩
  have hθeq : ∀ (a : X) (haT : a ∈ T) (haL : QuotientGroup.mk' (gnC T) a ∈ L),
      c.θ ⟨a, hAnL (hmA a haT haL)⟩ = e ⟨QuotientGroup.mk' (gnC T) a, haL⟩ := by
    intro a haT haL
    rw [SevenCtx0.θ, MonoidHom.comp_apply]
    rw [c.θs_of_mem_L (y := πN T L ⟨a, hAnL (hmA a haT haL)⟩) (by rw [coe_πN]; exact haL)]
    congr 1
  ext σ
  rw [c.mem_img hAnL]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haL : QuotientGroup.mk' (gnC T) a ∈ L := ha.2
    have haT : QuotientGroup.mk' (gnC T) a ∈ gnImg T T := ⟨a, ha.1, rfl⟩
    exact ⟨⟨QuotientGroup.mk' (gnC T) a, haL⟩, ⟨haT, haL⟩,
      (hθeq a ha.1 haL).symm⟩
  · rintro ⟨⟨x, hxL⟩, hxK, rfl⟩
    obtain ⟨hxT, hxL'⟩ := hxK
    obtain ⟨t, ht, htx⟩ := hxT
    have htL : QuotientGroup.mk' (gnC T) t ∈ L := htx ▸ hxL
    refine ⟨t, hmA t ht htL, ?_⟩
    exact (hθeq t ht htL).trans (congrArg e (Subtype.ext htx))

private theorem card_gnImg_inf (c : SevenCtx0 T L)
    {hSyl : IsSylowTwoOf (gnImg T T ⊓ (L : Subgroup (X ⧸ gnC T)))
      (L : Subgroup (X ⧸ gnC T))} : Nat.card ↥(gnImg T T ⊓ L) = 8 := by
  have hcardL : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥L).factorization 2 = 3 := by
    rw [hcardL]
    have h2520 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h2520, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  rw [hSyl.card_eq, twoPart, hfac]
  norm_num

theorem card_img_inf_lT (hX : GNSetting X T) (hL : IsComponentOf L ⊤) :
    Nat.card (c.img (T ⊓ lT T L)) = 8 ∧
      c.img (T ⊓ lT T L) ≤ alternatingGroup (Fin 7) := by
  classical
  have himg := img_inf_lT_eq c
  have hSyl := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hL.2.1
  have hcardK := card_gnImg_inf c (hSyl := hSyl)
  have hKL : gnImg T T ⊓ L ≤ L := inf_le_right
  have he_inj : Function.Injective
      ((alternatingGroup (Fin 7)).subtype.comp c.eL.toMonoidHom) := by
    intro x y hxy
    exact c.eL.injective (Subtype.ext hxy)
  constructor
  · rw [himg, Subgroup.card_map_of_injective he_inj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hcardK]
  · rw [himg]
    rintro _ ⟨x, -, rfl⟩
    exact (c.eL x).2
end

end SevenCtx0

namespace SevenCtx0

variable (c : SevenCtx0 T L)

private theorem wP_sup_normalizer {Rs : Subgroup (X ⧸ gnC T)} (hRL : Rs ≤ nLs T L)
    {Q P Pm : Subgroup (Perm (Fin 7))} (hQ : c.imgS Rs = Q) (hmin : MinParabolic P Q Pm) :
    Q ≤ P ∧ c.wP Pm ≤ c.wP P ∧ c.wP P ≤ nLs T L ∧ c.wP Pm ≤ nLs T L ∧
      c.wP P ⊔ Rs ≤ nLs T L ∧ Q ≤ Pm ∧
      (∀ r (hr : r ∈ Rs), c.θs ⟨r, hRL hr⟩ ∈ Q) ∧
      Rs ≤ Subgroup.normalizer (c.wP P : Set (X ⧸ gnC T)) ∧
      Rs ≤ Subgroup.normalizer (c.wP Pm : Set (X ⧸ gnC T)) := by
  have hQP : Q ≤ P := hmin.le.trans hmin.maximal.1.le
  have hWmW : c.wP Pm ≤ c.wP P := by
    intro x hx
    exact (c.mem_wP).2 ⟨((c.mem_wP).1 hx).1, hmin.maximal.1.le ((c.mem_wP).1 hx).2⟩
  have hWL : c.wP P ≤ nLs T L := (c.wP_le_L P).trans Subgroup.le_normalizer
  have hWmL : c.wP Pm ≤ nLs T L := (c.wP_le_L Pm).trans Subgroup.le_normalizer
  have hHL : c.wP P ⊔ Rs ≤ nLs T L := sup_le hWL hRL
  have hQm : Q ≤ Pm := hmin.le
  have hRQ : ∀ r (hr : r ∈ Rs), c.θs ⟨r, hRL hr⟩ ∈ Q := fun r hr =>
    hQ ▸ ⟨⟨r, hRL hr⟩, hr, rfl⟩
  have hRW : Rs ≤ Subgroup.normalizer (c.wP P : Set (X ⧸ gnC T)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Rs, ∀ w ∈ c.wP P, g * w * g⁻¹ ∈ c.wP P := by
      intro g hg w hw
      obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
      have hgw : g * w * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hRL hg) w).1 hwL
      refine (c.mem_wP).2 ⟨hgw, ?_⟩
      rw [c.hθs ⟨g, hRL hg⟩ ⟨w, hwL⟩ ⟨_, hgw⟩ rfl]
      exact P.mul_mem (P.mul_mem (hQP (hRQ g hg)) hwP) (P.inv_mem (hQP (hRQ g hg)))
    intro w
    constructor
    · exact key r hr w
    · intro h
      have := key r⁻¹ (Rs.inv_mem hr) _ h
      simpa [mul_assoc] using this
  have hRWm : Rs ≤ Subgroup.normalizer (c.wP Pm : Set (X ⧸ gnC T)) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Rs, ∀ w ∈ c.wP Pm, g * w * g⁻¹ ∈ c.wP Pm := by
      intro g hg w hw
      obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
      have hgw : g * w * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hRL hg) w).1 hwL
      refine (c.mem_wP).2 ⟨hgw, ?_⟩
      rw [c.hθs ⟨g, hRL hg⟩ ⟨w, hwL⟩ ⟨_, hgw⟩ rfl]
      exact Pm.mul_mem (Pm.mul_mem (hQm (hRQ g hg)) hwP) (Pm.inv_mem (hQm (hRQ g hg)))
    intro w
    constructor
    · exact key r hr w
    · intro h
      have := key r⁻¹ (Rs.inv_mem hr) _ h
      simpa [mul_assoc] using this
  exact ⟨hQP, hWmW, hWL, hWmL, hHL, hQm, hRQ, hRW, hRWm⟩

private theorem wP_sup_decomp {Rs : Subgroup (X ⧸ gnC T)} {P Pm : Subgroup (Perm (Fin 7))}
    (hRW : Rs ≤ Subgroup.normalizer (c.wP P : Set (X ⧸ gnC T)))
    (hRWm : Rs ≤ Subgroup.normalizer (c.wP Pm : Set (X ⧸ gnC T))) :
    (∀ h ∈ c.wP P ⊔ Rs, ∃ w ∈ c.wP P, ∃ r ∈ Rs, h = w * r) ∧
      (∀ h ∈ c.wP Pm ⊔ Rs, ∃ w ∈ c.wP Pm, ∃ r ∈ Rs, h = w * r) := by
  have hmul : ((c.wP P : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) =
      ((c.wP P ⊔ Rs : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left (c.wP P) Rs hRW).symm
  have hmulm : ((c.wP Pm : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) =
      ((c.wP Pm ⊔ Rs : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left (c.wP Pm) Rs hRWm).symm
  constructor
  · intro h hh
    have : h ∈ ((c.wP P : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) := by
      rw [hmul]; exact hh
    obtain ⟨w, hw, r, hr, rfl⟩ := this
    exact ⟨w, hw, r, hr, rfl⟩
  · intro h hh
    have : h ∈ ((c.wP Pm : Set (X ⧸ gnC T)) * (Rs : Set (X ⧸ gnC T))) := by
      rw [hmulm]; exact hh
    obtain ⟨w, hw, r, hr, rfl⟩ := this
    exact ⟨w, hw, r, hr, rfl⟩

private theorem wP_sup_ker {Rs : Subgroup (X ⧸ gnC T)} {P Q : Subgroup (Perm (Fin 7))}
    (hRL : Rs ≤ nLs T L) (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (hRQ : ∀ r (hr : r ∈ Rs), c.θs ⟨r, hRL hr⟩ ∈ Q)
    (hQL : ∀ σ ∈ Q ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T) (hy : y ∈ Rs ⊓ L),
      c.θs ⟨y, hRL hy.1⟩ = σ)
    (hdecomp : ∀ h ∈ c.wP P ⊔ Rs, ∃ w ∈ c.wP P, ∃ r ∈ Rs, h = w * r) :
    ∀ (h : X ⧸ gnC T) (hh : h ∈ c.wP P ⊔ Rs),
      c.θs ⟨h, hHL hh⟩ = 1 → h ∈ Rs := by
  intro h hh h1
  obtain ⟨w, hw, r, hr, rfl⟩ := hdecomp h hh
  obtain ⟨hwL, -⟩ := (c.mem_wP).1 hw
  have hθ : c.θs ⟨w, (sup_le ((c.wP_le_L P).trans Subgroup.le_normalizer) hRL)
      (Subgroup.mem_sup_left hw)⟩ * c.θs ⟨r, hRL hr⟩ = 1 := by
    rw [← map_mul]; exact h1
  have hθw : c.θs ⟨w, (sup_le ((c.wP_le_L P).trans Subgroup.le_normalizer) hRL)
      (Subgroup.mem_sup_left hw)⟩ = c.eL ⟨w, hwL⟩ :=
    c.θs_of_mem_L hwL
  have hrA : c.θs ⟨r, hRL hr⟩ ∈ Q ⊓ alternatingGroup (Fin 7) := by
    refine ⟨hRQ r hr, ?_⟩
    have : c.θs ⟨r, hRL hr⟩ = (c.θs ⟨w, (sup_le ((c.wP_le_L P).trans
        Subgroup.le_normalizer) hRL) (Subgroup.mem_sup_left hw)⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_right hθ
    rw [this, hθw]
    exact (alternatingGroup (Fin 7)).inv_mem (c.eL ⟨w, hwL⟩).2
  obtain ⟨y, hy, hyθ⟩ := hQL _ hrA
  have hwy : w * y ∈ L := L.mul_mem hwL hy.2
  have hθwy : c.θs ⟨w * y, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right hy.1))⟩ = 1 := by
    have e : (⟨w * y, hHL (Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
        (Subgroup.mem_sup_right hy.1))⟩ : ↥(nLs T L)) =
        ⟨w, (sup_le ((c.wP_le_L P).trans Subgroup.le_normalizer) hRL)
          (Subgroup.mem_sup_left hw)⟩ * ⟨y, hRL hy.1⟩ := rfl
    rw [e, map_mul, hyθ, hθ]
  have h2 : (c.eL ⟨w * y, hwy⟩ : Perm (Fin 7)) = 1 := by
    rw [← c.θs_of_mem_L (y := ⟨w * y, hHL (Subgroup.mul_mem _
      (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hy.1))⟩) hwy]
    exact hθwy
  have h3 : c.eL ⟨w * y, hwy⟩ = 1 := Subtype.ext h2
  have h4 : (⟨w * y, hwy⟩ : ↥L) = 1 := c.eL.injective (h3.trans (map_one c.eL).symm)
  have h5 : w * y = 1 := congrArg Subtype.val h4
  have hwR : w ∈ Rs := by
    rw [eq_inv_of_mul_eq_one_left h5]
    exact Rs.inv_mem hy.1
  exact Rs.mul_mem hwR hr

private theorem wP_sup_img {Rs : Subgroup (X ⧸ gnC T)} {Q P : Subgroup (Perm (Fin 7))}
    (hRL : Rs ≤ nLs T L) (hWL : c.wP P ≤ nLs T L) (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (hQ : c.imgS Rs = Q) (hQP : Q ≤ P)
    (hRQ : ∀ r (hr : r ∈ Rs), c.θs ⟨r, hRL hr⟩ ∈ Q)
    (hodd : P ≤ alternatingGroup (Fin 7) ∨ ∃ q ∈ Q, q ∉ alternatingGroup (Fin 7))
    (hQL : ∀ σ ∈ Q ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T) (hy : y ∈ Rs ⊓ L),
      c.θs ⟨y, hRL hy.1⟩ = σ)
    (hdecomp : ∀ h ∈ c.wP P ⊔ Rs, ∃ w ∈ c.wP P, ∃ r ∈ Rs, h = w * r) :
    c.imgS (c.wP P ⊔ Rs) = P := by
  apply le_antisymm
  · rintro _ ⟨⟨h, hh'⟩, hh, rfl⟩
    obtain ⟨w, hw, r, hr, rfl⟩ := hdecomp h hh
    obtain ⟨hwL, hwP⟩ := (c.mem_wP).1 hw
    have e : (⟨w * r, hh'⟩ : ↥(nLs T L)) = ⟨w, hWL hw⟩ * ⟨r, hRL hr⟩ := rfl
    rw [e, map_mul, c.θs_of_mem_L hwL]
    exact P.mul_mem hwP (hQP (hRQ r hr))
  · intro σ hσ
    have hA : ∀ τ ∈ P, τ ∈ alternatingGroup (Fin 7) → τ ∈ c.imgS (c.wP P ⊔ Rs) := by
      intro τ hτP hτA
      set w : ↥L := c.eL.symm ⟨τ, hτA⟩ with hwdef
      have hwW : (w : X ⧸ gnC T) ∈ c.wP P := by
        refine (c.mem_wP).2 ⟨w.2, ?_⟩
        rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply]
        exact hτP
      refine ⟨⟨w, hWL hwW⟩, Subgroup.mem_sup_left hwW, ?_⟩
      rw [c.θs_of_mem_L w.2]
      rw [show (⟨(w : X ⧸ gnC T), w.2⟩ : ↥L) = w from rfl, hwdef, MulEquiv.apply_symm_apply]
    rcases hodd with hPA | ⟨q, hqQ, hqA⟩
    · exact hA σ hσ (hPA hσ)
    · by_cases hσA : σ ∈ alternatingGroup (Fin 7)
      · exact hA σ hσ hσA
      · have hsq : σ * q⁻¹ ∈ alternatingGroup (Fin 7) := by
          rw [Equiv.Perm.mem_alternatingGroup] at hσA hqA ⊢
          rw [map_mul, map_inv]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · exact absurd h hσA
          rcases Int.units_eq_one_or (Equiv.Perm.sign q) with h' | h'
          · exact absurd h' hqA
          rw [h, h']; decide
        have h1 := hA (σ * q⁻¹) (P.mul_mem hσ (P.inv_mem (hQP hqQ))) hsq
        have h2 : q ∈ c.imgS (c.wP P ⊔ Rs) := by
          rw [← hQ] at hqQ
          obtain ⟨⟨r, hr'⟩, hr, rfl⟩ := hqQ
          exact ⟨⟨r, hr'⟩, Subgroup.mem_sup_right hr, rfl⟩
        have := (c.imgS (c.wP P ⊔ Rs)).mul_mem h1 h2
        simpa using this

private structure WPMap (c : SevenCtx0 T L) (H Rs : Subgroup (X ⧸ gnC T))
    (hHL : H ≤ nLs T L) (P Q : Subgroup (Perm (Fin 7))) where
  f : ↥H →* Perm (Fin 7)
  hf : f = c.θs.comp (Subgroup.inclusion hHL)
  hmapTop : (⊤ : Subgroup ↥H).map f = P
  hmapR : (Rs.subgroupOf H).map f = Q
  hkerf : f.ker ≤ Rs.subgroupOf H
  hmemTop : ∀ x, f x ∈ P
  hsurjTop : ∀ p, p ∈ P → ∃ x, f x = p
  hmemR : ∀ x, x ∈ Rs.subgroupOf H → f x ∈ Q
  hsurjR : ∀ q, q ∈ Q → ∃ x, x ∈ Rs.subgroupOf H ∧ f x = q

private noncomputable def wP_sup_map {Rs : Subgroup (X ⧸ gnC T)} {Q P : Subgroup (Perm (Fin 7))}
    (hRL : Rs ≤ nLs T L) (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (hQ : c.imgS Rs = Q) (himg : c.imgS (c.wP P ⊔ Rs) = P)
    (hker : ∀ (h : X ⧸ gnC T) (hh : h ∈ c.wP P ⊔ Rs),
      c.θs ⟨h, hHL hh⟩ = 1 → h ∈ Rs) :
    WPMap c (c.wP P ⊔ Rs) Rs hHL P Q := by
  let f : ↥(c.wP P ⊔ Rs) →* Perm (Fin 7) := c.θs.comp (Subgroup.inclusion hHL)
  have hmapTop : (⊤ : Subgroup ↥(c.wP P ⊔ Rs)).map f = P := by
    apply le_antisymm
    · rintro σ ⟨x, -, rfl⟩
      have hmem : f x ∈ c.imgS (c.wP P ⊔ Rs) := ⟨⟨x, hHL x.2⟩, x.2, rfl⟩
      rwa [himg] at hmem
    · intro σ hσ
      have hσ' : σ ∈ c.imgS (c.wP P ⊔ Rs) := by rwa [himg]
      obtain ⟨y, hy, rfl⟩ := hσ'
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hmapR : (Rs.subgroupOf (c.wP P ⊔ Rs)).map f = Q := by
    rw [← hQ]
    ext σ
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hHL r.2⟩, hr, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_sup_right hy⟩, hy, rfl⟩
  have hkerf : f.ker ≤ Rs.subgroupOf (c.wP P ⊔ Rs) := by
    intro x hx
    have hx1 : c.θs ⟨x, hHL x.2⟩ = 1 := hx
    exact hker x x.2 hx1
  have hmemTop : ∀ x : ↥(c.wP P ⊔ Rs), f x ∈ P := by
    intro x
    have hmem : f x ∈ c.imgS (c.wP P ⊔ Rs) := ⟨⟨x, hHL x.2⟩, x.2, rfl⟩
    rwa [himg] at hmem
  have hsurjTop : ∀ p, p ∈ P → ∃ x : ↥(c.wP P ⊔ Rs), f x = p := by
    intro p hp
    have hp' : p ∈ c.imgS (c.wP P ⊔ Rs) := by rwa [himg]
    obtain ⟨y, hy, rfl⟩ := hp'
    exact ⟨⟨y, hy⟩, rfl⟩
  have hmemR : ∀ x : ↥(c.wP P ⊔ Rs), x ∈ Rs.subgroupOf (c.wP P ⊔ Rs) → f x ∈ Q := by
    intro x hx
    have hx' : f x ∈ c.imgS Rs := ⟨⟨x, hHL x.2⟩, hx, rfl⟩
    rwa [hQ] at hx'
  have hsurjR : ∀ q, q ∈ Q → ∃ x : ↥(c.wP P ⊔ Rs),
      x ∈ Rs.subgroupOf (c.wP P ⊔ Rs) ∧ f x = q := by
    intro q hq
    have hq' : q ∈ c.imgS Rs := by rwa [hQ]
    obtain ⟨y, hy, rfl⟩ := hq'
    exact ⟨⟨y, Subgroup.mem_sup_right hy⟩, hy, rfl⟩
  exact ⟨f, rfl, hmapTop, hmapR, hkerf, hmemTop, hsurjTop, hmemR, hsurjR⟩

private theorem wP_sup_sylow {Rs : Subgroup (X ⧸ gnC T)} {Q P Pm : Subgroup (Perm (Fin 7))}
    (hRp : IsPGroup 2 Rs) (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q) (hmin : MinParabolic P Q Pm) :
    IsSylowTwoOf Rs (c.wP P ⊔ Rs) := by
  have hrel : Rs.relIndex (c.wP P ⊔ Rs) = Q.relIndex P := by
    have h1 := Subgroup.relIndex_map_map md.f (Rs.subgroupOf (c.wP P ⊔ Rs)) ⊤
    rw [md.hmapR, md.hmapTop, sup_eq_left.mpr md.hkerf, top_sup_eq,
      Subgroup.relIndex_top_right] at h1
    exact h1.symm
  refine ⟨le_sup_right, hRp, ?_⟩
  show ¬ 2 ∣ Rs.relIndex (c.wP P ⊔ Rs)
  rw [hrel]
  exact hmin.isSylow.2.2

private theorem wP_sup_notNormal {Rs : Subgroup (X ⧸ gnC T)} {Q P Pm : Subgroup (Perm (Fin 7))}
    (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q) (hmin : MinParabolic P Q Pm) :
    ¬ c.wP P ⊔ Rs ≤ Subgroup.normalizer (Rs : Set (X ⧸ gnC T)) := by
  intro hle
  apply hmin.not_normal
  have htopN : (⊤ : Subgroup ↥(c.wP P ⊔ Rs)) ≤
      Subgroup.normalizer (Rs.subgroupOf (c.wP P ⊔ Rs) : Set ↥(c.wP P ⊔ Rs)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq le_sup_right]
    exact fun x _ => hle x.2
  have hm : (⊤ : Subgroup ↥(c.wP P ⊔ Rs)).map md.f ≤
      (Subgroup.normalizer (Rs.subgroupOf (c.wP P ⊔ Rs) : Set ↥(c.wP P ⊔ Rs))).map md.f :=
    Subgroup.map_mono htopN
  have hn : (Subgroup.normalizer (Rs.subgroupOf (c.wP P ⊔ Rs) : Set ↥(c.wP P ⊔ Rs))).map md.f ≤
      Subgroup.normalizer (Q : Set (Perm (Fin 7))) := by
    have hle' := Subgroup.le_normalizer_map md.f (H := Rs.subgroupOf (c.wP P ⊔ Rs))
    rwa [md.hmapR] at hle'
  rintro p hp
  obtain ⟨x, rfl⟩ := md.hsurjTop p hp
  exact hn (hm ⟨x, Subgroup.mem_top x, rfl⟩)

private theorem wP_sup_comap {Rs : Subgroup (X ⧸ gnC T)} {Q P Pm : Subgroup (Perm (Fin 7))}
    (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q)
    (hdecomp : ∀ h ∈ c.wP P ⊔ Rs, ∃ w ∈ c.wP P, ∃ r ∈ Rs, h = w * r)
    (hdecompM : ∀ h ∈ c.wP Pm ⊔ Rs, ∃ w ∈ c.wP Pm, ∃ r ∈ Rs, h = w * r)
    (hWmW : c.wP Pm ≤ c.wP P) (hQm : Q ≤ Pm) :
    Pm.comap md.f = (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs) := by
  ext x
  constructor
  · intro hx
    have hxPm : md.f x ∈ Pm := hx
    obtain ⟨w, hw, r, hr, hxeq⟩ := hdecomp x x.2
    let xw : ↥(c.wP P ⊔ Rs) := ⟨w, Subgroup.mem_sup_left hw⟩
    let xr : ↥(c.wP P ⊔ Rs) := ⟨r, Subgroup.mem_sup_right hr⟩
    have hxsplit : x = xw * xr := by
      apply Subtype.ext
      simpa [xw, xr] using hxeq
    have hfx : md.f x = md.f xw * md.f xr := by rw [hxsplit, map_mul]
    have hfr : md.f xr ∈ Q := md.hmemR xr hr
    have hfw : md.f xw ∈ Pm := by
      have : md.f xw = md.f x * (md.f xr)⁻¹ := by rw [hfx]; group
      rw [this]
      exact Pm.mul_mem hxPm (Pm.inv_mem (hQm hfr))
    have hwL : (w : X ⧸ gnC T) ∈ L := (c.wP_le_L P) hw
    have hfwθ : md.f xw = c.eL ⟨w, hwL⟩ := by
      rw [md.hf]
      change c.θs ⟨w, hHL (Subgroup.mem_sup_left hw)⟩ = c.eL ⟨w, hwL⟩
      exact c.θs_of_mem_L hwL
    have hwWm : w ∈ c.wP Pm := by
      refine (c.mem_wP).2 ⟨hwL, ?_⟩
      rw [← hfwθ]
      exact hfw
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hxsplit]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwWm) (Subgroup.mem_sup_right hr)
  · intro hx
    have hxM := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨w, hw, r, hr, hxeq⟩ := hdecompM x hxM
    let xw : ↥(c.wP P ⊔ Rs) := ⟨w, Subgroup.mem_sup_left (hWmW hw)⟩
    let xr : ↥(c.wP P ⊔ Rs) := ⟨r, Subgroup.mem_sup_right hr⟩
    have hxsplit : x = xw * xr := by
      apply Subtype.ext
      simpa [xw, xr] using hxeq
    have hfx : md.f x = md.f xw * md.f xr := by rw [hxsplit, map_mul]
    have hfw : md.f xw ∈ Pm := by
      have hwL : (w : X ⧸ gnC T) ∈ L := (c.wP_le_L Pm) hw
      rw [md.hf]
      change c.θs ⟨w, hHL (Subgroup.mem_sup_left (hWmW hw))⟩ ∈ Pm
      rw [c.θs_of_mem_L hwL]
      exact ((c.mem_wP).1 hw).2
    have hfr : md.f xr ∈ Q := md.hmemR xr hr
    change md.f x ∈ Pm
    rw [hfx]
    exact Pm.mul_mem hfw (hQm hfr)

private noncomputable def wP_sup_mapM {Rs : Subgroup (X ⧸ gnC T)} {Q P Pm : Subgroup (Perm (Fin 7))}
    (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q) (hmin : MinParabolic P Q Pm)
    (hcomap : Pm.comap md.f = (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)) :
    ((c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)).map md.f = Pm := by
  rw [← hcomap]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro p hp
    obtain ⟨x, hx⟩ := md.hsurjTop p (hmin.maximal.1.le hp)
    exact ⟨x, show md.f x ∈ Pm by rw [hx]; exact hp, hx⟩

private theorem wP_sup_max {Rs : Subgroup (X ⧸ gnC T)} {Q P Pm : Subgroup (Perm (Fin 7))}
    (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q) (hmin : MinParabolic P Q Pm)
    (hcomap : Pm.comap md.f = (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs))
    (hmapM : ((c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)).map md.f = Pm) :
    IsMaxSubgroupIn (c.wP P ⊔ Rs) (c.wP Pm ⊔ Rs) := by
  have hmMH : c.wP Pm ⊔ Rs ≤ c.wP P ⊔ Rs := by
    refine sup_le ?_ le_sup_right
    intro x hx
    exact Subgroup.mem_sup_left ((c.mem_wP).2 ⟨((c.mem_wP).1 hx).1,
      hmin.maximal.1.le ((c.mem_wP).1 hx).2⟩)
  refine ⟨lt_of_le_of_ne hmMH (fun heq => ?_), fun K hMK hKH => ?_⟩
  · have h1 : ((c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)).map md.f =
        ((c.wP P ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)).map md.f := by rw [heq]
    rw [hmapM, Subgroup.subgroupOf_self, md.hmapTop] at h1
    exact hmin.maximal.1.ne h1
  · have hkerK : md.f.ker ≤ K.subgroupOf (c.wP P ⊔ Rs) :=
      md.hkerf.trans (Subgroup.subgroupOf_mono _ (le_sup_right.trans hMK.le))
    have hK' : (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs) <
        K.subgroupOf (c.wP P ⊔ Rs) := by
      refine lt_of_le_of_ne (Subgroup.subgroupOf_mono _ hMK.le) fun heq => ?_
      have hmap_eq : (c.wP Pm ⊔ Rs) = K := by
        have h := congrArg (Subgroup.map (c.wP P ⊔ Rs).subtype) heq
        rwa [Subgroup.map_subgroupOf_eq_of_le hmMH,
          Subgroup.map_subgroupOf_eq_of_le hKH] at h
      exact hMK.ne hmap_eq
    have hle : Pm ≤ (K.subgroupOf (c.wP P ⊔ Rs)).map md.f := by
      rw [← hmapM]
      exact Subgroup.map_mono hK'.le
    have hne : (K.subgroupOf (c.wP P ⊔ Rs)).map md.f ≠ Pm := by
      intro heq
      have hx : K.subgroupOf (c.wP P ⊔ Rs) =
          ((K.subgroupOf (c.wP P ⊔ Rs)).map md.f).comap md.f :=
        (Subgroup.comap_map_eq_self hkerK).symm
      rw [heq, hcomap] at hx
      exact hK'.ne hx.symm
    have hKmap : (K.subgroupOf (c.wP P ⊔ Rs)).map md.f = P :=
      hmin.maximal.2 _ (lt_of_le_of_ne hle hne.symm)
        (by rintro _ ⟨x, -, rfl⟩; exact md.hmemTop x)
    have htop : K.subgroupOf (c.wP P ⊔ Rs) = ⊤ := by
      calc K.subgroupOf (c.wP P ⊔ Rs) =
            ((K.subgroupOf (c.wP P ⊔ Rs)).map md.f).comap md.f :=
            (Subgroup.comap_map_eq_self hkerK).symm
        _ = P.comap md.f := congrArg (fun A => A.comap md.f) hKmap
        _ = ⊤ := by
          rw [eq_top_iff]
          intro x _
          exact md.hmemTop x
    exact le_antisymm hKH (Subgroup.subgroupOf_eq_top.mp htop)

private structure WPG (H Rs : Subgroup (X ⧸ gnC T)) (P Q : Subgroup (Perm (Fin 7))) where
  g : ↥H →* ↥P
  hg : Function.Surjective g
  hker_g : g.ker ≤ Rs.subgroupOf H
  hmapQ : (Rs.subgroupOf H).map g = Q.subgroupOf P

private noncomputable def wP_sup_g {Rs : Subgroup (X ⧸ gnC T)} {Q P : Subgroup (Perm (Fin 7))}
    (hHL : c.wP P ⊔ Rs ≤ nLs T L)
    (md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q) (hQP : Q ≤ P) :
    WPG (c.wP P ⊔ Rs) Rs P Q := by
  have hfP : ∀ x : ↥(c.wP P ⊔ Rs), md.f x ∈ P := md.hmemTop
  let g : ↥(c.wP P ⊔ Rs) →* ↥P := md.f.codRestrict P hfP
  have hg : Function.Surjective g := by
    intro p
    obtain ⟨x, hx⟩ := md.hsurjTop p p.2
    exact ⟨x, Subtype.ext hx⟩
  have hker_g : g.ker ≤ Rs.subgroupOf (c.wP P ⊔ Rs) := by
    intro x hx
    apply md.hkerf
    have hx1 : md.f x = 1 := Subtype.ext_iff.mp hx
    exact hx1
  have hmapQ : (Rs.subgroupOf (c.wP P ⊔ Rs)).map g = Q.subgroupOf P := by
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact md.hmemR r hr
    · intro hq
      obtain ⟨r, hr, hrg⟩ := md.hsurjR (q : Perm (Fin 7)) hq
      exact ⟨r, hr, Subtype.ext hrg⟩
  exact ⟨g, hg, hker_g, hmapQ⟩

private theorem wP_sup_unique {Rs : Subgroup (X ⧸ gnC T)}
    {Q P Pm : Subgroup (Perm (Fin 7))} (hmin : MinParabolic P Q Pm) (hQP : Q ≤ P)
    (qd : WPG (c.wP P ⊔ Rs) Rs P Q)
    (hcomap : (Pm.subgroupOf P).comap qd.g =
      (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs)) :
    ∀ N, IsMaxSubgroupIn (c.wP P ⊔ Rs) N → Rs ≤ N → N = c.wP Pm ⊔ Rs := by
  intro N hN hRN
  have hNM : N ≤ c.wP P ⊔ Rs := hN.1.le
  have hkerN : qd.g.ker ≤ N.subgroupOf (c.wP P ⊔ Rs) :=
    qd.hker_g.trans (Subgroup.subgroupOf_mono _ hRN)
  have hNcoatom : IsCoatom (N.subgroupOf (c.wP P ⊔ Rs)) :=
    B6.isMaxSubgroupIn_top_iff.mp (B6.isMaxSubgroupIn_top_subgroupOf hN)
  have hKcoatom : IsCoatom ((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g) :=
    B6.isCoatom_map_of_surjective qd.hg hkerN hNcoatom
  have hKmax_inP : IsMaxSubgroupIn (⊤ : Subgroup ↥P)
      ((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g) :=
    B6.isMaxSubgroupIn_top_iff.mpr hKcoatom
  have hKmax : IsMaxSubgroupIn P (((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g).map P.subtype) :=
    B6.isMaxSubgroupIn_map_subtype hKmax_inP
  have hQK : Q ≤ (((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g).map P.subtype) := by
    have h1 : Q.subgroupOf P ≤ (N.subgroupOf (c.wP P ⊔ Rs)).map qd.g := by
      rw [← qd.hmapQ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hRN)
    have h1' := Subgroup.map_mono (f := P.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hQP] at h1'
  have hK_eq : (((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g).map P.subtype) = Pm :=
    hmin.eq_of_maximal hKmax hQK
  have hNmap : (N.subgroupOf (c.wP P ⊔ Rs)).map qd.g = Pm.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hK_eq, Subgroup.map_subgroupOf_eq_of_le hmin.maximal.1.le]
  have hN_eq : N.subgroupOf (c.wP P ⊔ Rs) =
      (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs) := by
    calc N.subgroupOf (c.wP P ⊔ Rs) =
          ((N.subgroupOf (c.wP P ⊔ Rs)).map qd.g).comap qd.g :=
          (Subgroup.comap_map_eq_self hkerN).symm
      _ = (Pm.subgroupOf P).comap qd.g := by rw [hNmap]
      _ = (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs) := hcomap
  have h := Subgroup.subgroupOf_inj.mp hN_eq
  have hMH : c.wP Pm ⊔ Rs ≤ c.wP P ⊔ Rs := by
    refine sup_le ?_ le_sup_right
    intro x hx
    exact Subgroup.mem_sup_left ((c.mem_wP).2 ⟨((c.mem_wP).1 hx).1,
      hmin.maximal.1.le ((c.mem_wP).1 hx).2⟩)
  rwa [inf_of_le_left hNM, inf_of_le_left hMH] at h

theorem minParabolic_wP_gen {Rs : Subgroup (X ⧸ gnC T)}
    (hRL : Rs ≤ nLs T L) (hRp : IsPGroup 2 Rs) {Q P Pm : Subgroup (Perm (Fin 7))}
    (hQ : c.imgS Rs = Q) (hmin : MinParabolic P Q Pm)
    (hodd : P ≤ alternatingGroup (Fin 7) ∨ ∃ q ∈ Q, q ∉ alternatingGroup (Fin 7))
    (hQL : ∀ σ ∈ Q ⊓ alternatingGroup (Fin 7), ∃ (y : X ⧸ gnC T) (hy : y ∈ Rs ⊓ L),
      c.θs ⟨y, hRL hy.1⟩ = σ) :
    MinParabolic (c.wP P ⊔ Rs) Rs (c.wP Pm ⊔ Rs) ∧ c.imgS (c.wP P ⊔ Rs) = P ∧
      ∀ y : ↥(nLs T L), (y : X ⧸ gnC T) ∈ c.wP P ⊔ Rs → c.θs y = 1 → (y : X ⧸ gnC T) ∈ Rs := by
  classical
  obtain ⟨hQP, hWmW, hWL, hWmL, hHL, hQm, hRQ, hRW, hRWm⟩ :=
    wP_sup_normalizer c hRL hQ hmin
  obtain ⟨hdecomp, hdecompM⟩ := wP_sup_decomp c hRW hRWm
  have hker := wP_sup_ker c hRL hHL hRQ hQL hdecomp
  have himg := wP_sup_img c hRL hWL hHL hQ hQP hRQ hodd hQL hdecomp
  let md : WPMap c (c.wP P ⊔ Rs) Rs hHL P Q := wP_sup_map c hRL hHL hQ himg hker
  have hSyl := wP_sup_sylow c hRp hHL md hmin
  have hnot := wP_sup_notNormal c hHL md hmin
  have hcomap_f := wP_sup_comap c hHL md hdecomp hdecompM hWmW hQm
  have hmapM := wP_sup_mapM c hHL md hmin hcomap_f
  have hmaxM := wP_sup_max c hHL md hmin hcomap_f hmapM
  let qd : WPG (c.wP P ⊔ Rs) Rs P Q := wP_sup_g c hHL md hQP
  have hcomap_g : (Pm.subgroupOf P).comap qd.g =
      (c.wP Pm ⊔ Rs).subgroupOf (c.wP P ⊔ Rs) := by
    rw [← hcomap_f]
    rfl
  have huniq : IsUniqueMaxOver (c.wP P ⊔ Rs) Rs (c.wP Pm ⊔ Rs) :=
    isUniqueMaxOver_iff.mpr ⟨hmaxM, le_sup_right,
      fun N hN hRN => wP_sup_unique c hmin hQP qd hcomap_g N hN hRN⟩
  exact ⟨⟨hSyl, hnot, huniq⟩, himg, fun y hy h1 => hker y hy h1⟩
end SevenCtx0

namespace SevenCtx0

variable (c : SevenCtx0 T L)

@[expose] noncomputable def conj (c : SevenCtx0 T L) (σ : Perm (Fin 7)) : SevenCtx0 T L where
  eL := c.eL.trans (conjA7 σ)
  θs := (MulAut.conj σ).toMonoidHom.comp c.θs
  hθs := by
    intro y l l' h
    simp only [MulEquiv.trans_apply, coe_conjA7, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [c.hθs y l l' h]
    group
  hθsL := by
    intro y l h
    simp only [MulEquiv.trans_apply, coe_conjA7, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [c.hθsL y l h]
  hθs1 := by
    intro y
    rw [← c.hθs1 y]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro h
      calc c.θs y = σ⁻¹ * (σ * c.θs y * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]; group

theorem img_conj (c : SevenCtx0 T L) (σ : Perm (Fin 7)) (A : Subgroup X) :
    (c.conj σ).img A = (c.img A).map (MulAut.conj σ).toMonoidHom := by
  rw [SevenCtx0.img, SevenCtx0.img, Subgroup.map_map]
  rfl

end SevenCtx0

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
