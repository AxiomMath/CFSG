module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFMod
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFRep
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFComp

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem L34FF.pCore_two_autOn_eq_bot (hR : IsPGroup 3 R)
    (hmap : ((L34FF.threeComp H R K).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K)
    (hdich : ∀ {N : Subgroup G}, N ≤ L34FF.threeComp H R K →
      L34FF.threeComp H R K ≤ Subgroup.normalizer (N : Set G) →
      N ≤ L34FF.threeCompCore H R K ∨ L34FF.threeComp H R K ≤ N)
    (hnot : ¬ L34FF.threeComp H R K ≤ L34FF.threeCompCore H R K)
    {D₀ V W Z : Subgroup G} (hD₀H : D₀ ≤ H) (hV : IsSylowTwoOf V D₀)
    (hcent : ∀ {l v : G}, l ∈ L34FF.threeComp H R K → v ∈ V → ∀ hlv : l * v ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨l * v, hlv⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) → l * v ∈ D₀)
    (hXW : L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (W : Set G))
    (hVZ : V ≤ Subgroup.centralizer (Z : Set G))
    (hW : ∀ D : Subgroup G, L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.centralizer (Z : Set G) → D ≤ Subgroup.centralizer (W : Set G))
    (hZW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (Z : Set G))
    (hβ : L34FF.threeComp H R K ⊓ Subgroup.centralizer (W : Set G) ≤
      L34FF.threeCompCore H R K) :
    CFSG.pCore 2 (autOn (L34FF.threeComp H R K ⊔ V) W) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  set Y := L34FF.threeCompCore H R K with hYdef
  set X := L ⊔ V with hXdef
  set f := L34FF.conjOnto W X hXW with hf
  have hLH : L ≤ H := L34FF.threeComp_le
  have hVH : V ≤ H := hV.1.trans hD₀H
  have hXH : X ≤ H := sup_le hLH hVH
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := hVH.trans L34FF.le_normalizer_threeComp
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := hXH.trans L34FF.le_normalizer_threeComp
  have hXCW := L34FF.le_normalizer_centralizer_of_normalizes hXW
  have hT : IsPGroup 3 (d1LiftX 3 H R K) := hR.to_le (d1LiftX_le 3 H R K)
  show sSup _ = ⊥
  rw [sSup_eq_bot]
  rintro N ⟨hNn, hN2⟩
  set D := (N.comap f).map X.subtype with hD
  have hDX : D ≤ X := Subgroup.map_subtype_le _
  have hmemD : ∀ x : X, (x : G) ∈ D ↔ f x ∈ N := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · exact fun h => ⟨x, h, rfl⟩
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    have key : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
      intro x hx d hdD
      have hdX := hDX hdD
      refine (hmemD ⟨x * d * x⁻¹, X.mul_mem (X.mul_mem hx hdX) (X.inv_mem hx)⟩).mpr ?_
      have e : (⟨x * d * x⁻¹, X.mul_mem (X.mul_mem hx hdX) (X.inv_mem hx)⟩ : X) =
          ⟨x, hx⟩ * ⟨d, hdX⟩ * (⟨x, hx⟩ : X)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hNn.conj_mem _ ((hmemD ⟨d, hdX⟩).mp hdD) _
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨key x hx d, fun hd' => ?_⟩
    have := key x⁻¹ (X.inv_mem hx) _ hd'
    simpa [mul_assoc] using this
  have hDL : D ⊓ L ≤ Y := by
    have hLDL : L ≤ Subgroup.normalizer ((D ⊓ L : Subgroup G) : Set G) :=
      L34FF.le_normalizer_inf_of_normalizes_both (le_sup_left.trans hXD) (le_sup_left.trans hXL)
    rcases hdich (N := D ⊓ L) inf_le_right hLDL with h | h
    · exact h
    · exfalso
      refine hnot fun l hl => hβ ⟨hl, ?_⟩
      revert l
      change L ≤ Subgroup.centralizer (W : Set G)
      refine L34FF.threeComp_le_of_forall fun g hg t ht => ?_
      have hyL : g * t * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (L34FF.le_normalizer_threeComp hg) t).mp
          (L34FF.d1LiftX_le_threeComp ht)
      obtain ⟨a, ha⟩ := L34FF.exists_pow_conj_eq_one (g := g) hT ht
      have hfy : f ⟨g * t * g⁻¹, Subgroup.mem_sup_left hyL⟩ ∈ N := (hmemD _).mp (h hyL).1
      obtain ⟨b, hb⟩ := hN2 ⟨_, hfy⟩
      have h2 : (f ⟨g * t * g⁻¹, Subgroup.mem_sup_left hyL⟩) ^ 2 ^ b = 1 := by
        simpa using congrArg Subtype.val hb
      have h3 : (f ⟨g * t * g⁻¹, Subgroup.mem_sup_left hyL⟩) ^ 3 ^ a = 1 := by
        rw [← map_pow]
        have : (⟨g * t * g⁻¹, Subgroup.mem_sup_left hyL⟩ : X) ^ 3 ^ a = 1 :=
          Subtype.ext (by simpa using ha)
        rw [this, map_one]
      exact (L34FF.conjOnto_eq_one_iff hXW _).mp
        (L34FF.eq_one_of_pow_three_pow_of_pow_two_pow h3 h2)
  have hDD₀ : D ≤ D₀ := by
    intro d hdD
    have hdX := hDX hdD
    have hdH := hXH hdX
    have hdC : π ⟨d, hdH⟩ ∈
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : k ∈ (L.subgroupOf H).map π := by rw [hmap]; exact hk
      obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hk'
      have hlL : l ∈ L := hl
      have h1 : d * l * d⁻¹ * l⁻¹ ∈ D := by
        have : l * d⁻¹ * l⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (hXD (Subgroup.mem_sup_left hlL)) _).mp (D.inv_mem hdD)
        have h' := D.mul_mem hdD this
        simpa only [mul_assoc] using h'
      have h2 : d * l * d⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXL hdX) l).mp hlL) (L.inv_mem hlL)
      have h3 := (hDL ⟨h1, h2⟩).2
      have hmem : d * l * d⁻¹ * l⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.mul_mem hdH hlH) (H.inv_mem hdH)) (H.inv_mem hlH)
      have h4 := (mk'_primeComplementCore_eq_one_iff 3 ⟨_, hmem⟩).mpr h3
      have e : (⟨d * l * d⁻¹ * l⁻¹, hmem⟩ : H) =
          ⟨d, hdH⟩ * ⟨l, hlH⟩ * (⟨d, hdH⟩ : H)⁻¹ * (⟨l, hlH⟩ : H)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h4
      have h5 := mul_inv_eq_one.mp h4
      rw [mul_inv_eq_iff_eq_mul] at h5
      exact h5.symm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L V hVL] at hdX
    obtain ⟨l, hl, v, hv, rfl⟩ := hdX
    exact hcent hl hv hdH hdC
  have hsylD : IsSylowTwoOf (V ⊓ D) D :=
    L34FF.isSylowTwoOf_inf_of_le_of_normalizes hV hDD₀ (le_sup_right.trans hXD)
  have hmapD : (D.subgroupOf X).map f = N := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemD x).mp hx
    · intro hφ
      obtain ⟨x, rfl⟩ := L34FF.conjOnto_surjective hXW φ
      exact ⟨x, (hmemD x).mpr hφ, rfl⟩
  have hcardN : (D ⊓ Subgroup.centralizer (W : Set G)).relIndex D = Nat.card N := by
    rw [← L34FF.card_map_conjOnto hXW hDX, hmapD]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hN2
  have hVDN : V ⊓ D ≤ Subgroup.normalizer
      ((D ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) :=
    L34FF.le_normalizer_inf_of_normalizes_both ((inf_le_left.trans le_sup_right).trans hXD)
      ((inf_le_left.trans le_sup_right).trans hXCW)
  have hED : (D ⊓ Subgroup.centralizer (W : Set G)) ⊔ (V ⊓ D) ≤ D := sup_le inf_le_left inf_le_right
  have h1 : ((D ⊓ Subgroup.centralizer (W : Set G)) ⊔ (V ⊓ D)).relIndex D ∣
      (V ⊓ D).relIndex D := by
    rw [← Subgroup.relIndex_mul_relIndex (V ⊓ D) _ D le_sup_right hED]
    exact dvd_mul_left _ _
  have h2 : ((D ⊓ Subgroup.centralizer (W : Set G)) ⊔ (V ⊓ D)).relIndex D ∣ 2 ^ m := by
    rw [← hm, ← hcardN, ← Subgroup.relIndex_mul_relIndex (D ⊓ Subgroup.centralizer (W : Set G))
      _ D le_sup_left hED]
    exact dvd_mul_left _ _
  have hodd : Nat.Coprime (((D ⊓ Subgroup.centralizer (W : Set G)) ⊔ (V ⊓ D)).relIndex D)
      (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hsylD.2.2).symm)
  have hDE : D ≤ (D ⊓ Subgroup.centralizer (W : Set G)) ⊔ (V ⊓ D) :=
    Subgroup.relIndex_eq_one.mp (Nat.Coprime.eq_one_of_dvd hodd h2)
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) := by
    intro d hd'
    have := hDE hd'
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hVDN] at this
    obtain ⟨c, hc, v, hv, rfl⟩ := this
    exact Subgroup.mul_mem _ (hZW hc.2) (hVZ hv.1)
  have hDW := hW D hXD hDZ
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨x, rfl⟩ := L34FF.conjOnto_surjective hXW φ
  rw [Subgroup.mem_bot]
  exact (L34FF.conjOnto_eq_one_iff hXW x).mpr (hDW ((hmemD x).mpr hφ))

theorem D1OneSmallData.pCore_two_autOn_eq_bot (hd : D1OneSmallData 3 P M H R Rbar K)
    (hL : IsLinThreeFour K) {V W Z : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M)))
    (hXW : L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (W : Set G))
    (hVZ : V ≤ Subgroup.centralizer (Z : Set G))
    (hW : ∀ D : Subgroup G, L34FF.threeComp H R K ⊔ V ≤ Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.centralizer (Z : Set G) → D ≤ Subgroup.centralizer (W : Set G))
    (hZW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (Z : Set G))
    (hβ : L34FF.threeComp H R K ⊓ Subgroup.centralizer (W : Set G) ≤
      L34FF.threeCompCore H R K) :
    CFSG.pCore 2 (autOn (L34FF.threeComp H R K ⊔ V) W) = ⊥ := by
  have hVH : V ≤ H := hV.1.trans ((glbPrimeCore_le 3 _).trans inf_le_left)
  exact L34FF.pCore_two_autOn_eq_bot hd.cfg.ext.isPGroup hd.map_threeComp hd.threeComp_dichotomy
    hd.not_threeComp_le_threeCompCore ((glbPrimeCore_le 3 _).trans inf_le_left) hV
    (fun {l v} hl hv hlv hC => by
      have hlH : l ∈ H := L34FF.threeComp_le hl
      have hvH : v ∈ H := hVH hv
      have hlK : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨l, hlH⟩ ∈ K := by
        rw [← hd.map_threeComp]
        exact ⟨⟨l, hlH⟩, hl, rfl⟩
      have he : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨v, hvH⟩ =
          (QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨l, hlH⟩)⁻¹ *
            QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨l * v, hlv⟩ := by
        have e : (⟨l * v, hlv⟩ : H) = ⟨l, hlH⟩ * ⟨v, hvH⟩ := rfl
        rw [e, map_mul, inv_mul_cancel_left]
      obtain ⟨a, ha⟩ := hV.2.1 ⟨v, hv⟩
      have hva : v ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
      have h1 := hd.eq_one_of_mk_eq_mul hL (hV.1 hv) hva hvH (K.inv_mem hlK) hC he
      have hlO : l ∈ GLBPrimeCore 3 H :=
        (mk'_primeComplementCore_eq_one_iff 3 ⟨l, hlH⟩).mp (inv_eq_one.mp h1)
      exact (GLBPrimeCore 3 (H ⊓ M)).mul_mem (hd.glbPrimeCore_le_inf hlO) (hV.1 hv))
    hXW hVZ hW hZW hβ

theorem L34FF.Core.isLinThreeFour_map_conjOnto (hd : L34FF.Core H R Rbar K)
    (hL : IsLinThreeFour K) {W X : Subgroup G} (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hLX : L34FF.threeComp H R K ≤ X)
    (hβ : L34FF.threeComp H R K ⊓ Subgroup.centralizer (W : Set G) ≤
      L34FF.threeCompCore H R K) :
    IsLinThreeFour (((L34FF.threeComp H R K).subgroupOf X).map (L34FF.conjOnto W X hXW) ⧸
      primeComplementCore (G := ((L34FF.threeComp H R K).subgroupOf X).map
        (L34FF.conjOnto W X hXW)) 3) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set L := L34FF.threeComp H R K with hLdef
  set f := L34FF.conjOnto W X hXW with hf
  have hLH : L ≤ H := L34FF.threeComp_le
  have hcopY := L34FF.coprime_card_threeCompCore (H := H) (R := R) (K := K)
  have hcop : ∀ N : Subgroup L, N.map L.subtype ≤ L34FF.threeCompCore H R K →
      Nat.Coprime 3 (Nat.card N) := by
    intro N hN
    rw [← Subgroup.card_map_of_injective L.subtype_injective]
    exact (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hN) hcopY).symm
  set g₁ : L →* (L.subgroupOf X).map f := (f.comp (Subgroup.inclusion hLX)).codRestrict _
    (fun l => ⟨Subgroup.inclusion hLX l, l.2, rfl⟩) with hg₁
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk₁ : Nat.Coprime 3 (Nat.card g₁.ker) := by
    refine hcop _ ?_
    rintro _ ⟨l, hl, rfl⟩
    refine hβ ⟨l.2, (L34FF.conjOnto_eq_one_iff hXW (Subgroup.inclusion hLX l)).mp ?_⟩
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    exact this
  have hmapK : ∀ l : L, π (Subgroup.inclusion hLH l) ∈ K := fun l => by
    rw [← hd.map_threeComp]
    exact ⟨Subgroup.inclusion hLH l, l.2, rfl⟩
  set g₂ : L →* K := (π.comp (Subgroup.inclusion hLH)).codRestrict K hmapK with hg₂
  have hg₂s : Function.Surjective g₂ := by
    rintro ⟨k, hk⟩
    have hk' : k ∈ (L.subgroupOf H).map π := by rw [hd.map_threeComp]; exact hk
    obtain ⟨⟨l, hlH⟩, hl, rfl⟩ := hk'
    exact ⟨⟨l, hl⟩, rfl⟩
  have hk₂ : Nat.Coprime 3 (Nat.card g₂.ker) := by
    refine hcop _ ?_
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨l.2, (mk'_primeComplementCore_eq_one_iff 3 (Subgroup.inclusion hLH l)).mp ?_⟩
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  have hLL := L34FF.isLinThreeFour_quotient hL g₂ hg₂s hk₂
  obtain ⟨e⟩ := L34FF.nonempty_quotient_primeComplementCore_mulEquiv Nat.prime_three g₁ hg₁s hk₁
  exact L34FF.isLinThreeFour_of_equiv e.symm hLL

end CFSG.AGLEmbedding
