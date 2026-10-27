module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviChart
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeLeviNormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeGen

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock longInv suppGroup coords
  IsAdaptedShortIn shortBlock weylMat)
open CFSG.ClassicalInvolution.RouteD.LeviModel
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type} [Group G]

theorem commute_of_mem_oddNormal {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) {T N Y : Subgroup G} (e : T ≃* SL(2, F)) (hNodd : Odd (Nat.card N))
    (hTY : T ≤ Y) (hnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) {g : G} (hg : g ∈ N)
    (hgT : ∀ t ∈ T, g * t * g⁻¹ ∈ T) : ∀ t ∈ T, g * t = t * g := by
  have hN' : (N.subgroupOf T).Normal := by
    refine ⟨fun n hn t => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm _ (hTY t.2) _ hn
  have hodd' : Odd (Nat.card (N.subgroupOf T)) := by
    refine hNodd.of_dvd_nat ?_
    have h1 : Nat.card (N.subgroupOf T) = Nat.card ((N.subgroupOf T).map T.subtype) :=
      (Subgroup.card_map_of_injective T.subtype_injective).symm
    rw [h1, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hbot := CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 hodd h3 e _ hN' hodd'
  intro t ht
  have hc : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have : g * (t * g⁻¹ * t⁻¹) ∈ N := N.mul_mem hg (by
      have := hnorm t (hTY ht) g⁻¹ (N.inv_mem hg)
      simpa [mul_assoc] using this)
    simpa [mul_assoc] using this
  have hcT : g * t * g⁻¹ * t⁻¹ ∈ T := T.mul_mem (hgT t ht) (T.inv_mem ht)
  have hmem : (⟨g * t * g⁻¹ * t⁻¹, hcT⟩ : T) ∈ N.subgroupOf T := hc
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg Subtype.val hmem
  simp only at this
  have h2 : g * t * g⁻¹ = t := by
    have := mul_inv_eq_one.mp this
    exact this
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [h2]

theorem oddNormal_commute_of_klein [Finite G] {Y N V : Subgroup G}
    (hnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) (hVY : V ≤ Y)
    (hV : IsKleinFour V)
    (hloc : ∀ v ∈ V, v ≠ 1 → ∀ g ∈ N, g * v = v * g → ∀ y ∈ Y, g * y = y * g) :
    ∀ g ∈ N, ∀ y ∈ Y, g * y = y * g := by
  have hpower : ∀ member : V, member ^ 2 = 1 := fun v => by
    simpa only [pow_two] using IsKleinFour.mul_self v
  have hcard : Nat.card V = 2 ^ 2 := by rw [IsKleinFour.card_four]; norm_num
  have hnormalized : V ≤ Subgroup.normalizer (N : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnorm v (hVY hv) h hh
    · intro hh
      have := hnorm v⁻¹ (Y.inv_mem (hVY hv)) _ hh
      simpa [mul_assoc] using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V N hpower hcard hNodd.not_two_dvd_nat hnormalized
  have hle : N ≤ Subgroup.centralizer (Y : Set G) := by
    rw [hgen]
    refine iSup₂_le fun v hv => ?_
    intro g hg
    obtain ⟨hgN, hgc⟩ := hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hvne : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
    have := hloc v v.2 hvne g hgN (Subgroup.mem_centralizer_singleton_iff.mp hgc) y hy
    exact this.symm
  intro g hg y hy
  exact ((Subgroup.mem_centralizer_iff.mp (hle hg)) y hy).symm

theorem ringChar_ne_two_of_two_ne_zero' {F : Type} [Field F] (h : (2 : F) ≠ 0) :
    ringChar F ≠ 2 := fun h2 => h (by
  have := ringChar.Nat.cast_ringChar (R := F)
  rw [h2] at this
  simpa using this)

end Generic

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem zf_ne_of_ne (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) {i j : Fin 3}
    (hij : i ≠ j) : Fr.zf i ≠ Fr.zf j := by
  intro h
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (Fr.mem i) (Fr.clsW S i)
    (S.shape.conj S.conjInvariant (Fr.gf i))
  refine typeC_not_mem_of_ne S.two_le S.five S.inClass S.exact (Fr.mem i) (Fr.clsW S i)
    (Fr.p1W S i) d (Fr.mem_centW S j i) (Fr.ne_of_neW S hij.symm) ?_
  rw [h]
  exact Frame.zf_memW S j

theorem node_facts (S : CSetupW p f 2 Ω K z) (Fr : Frame p f 2 Ω K z) {l i j : Fin 3}
    (LF : LocalFrameI Fr l) (hi : l.succAbove 0 = i) (hj : l.succAbove 1 = j) {T : Subgroup G}
    (hT : T ≤ Mf Fr i j) (hA : IsAdaptedShortIn (Mf Fr i j) (Fr.Tf i) (Fr.Tf j) (Fr.zf i) T) :
    Nonempty (SL(2, GaloisField p f) ≃* T) ∧ Fr.zf i * Fr.zf j ∈ T ∧
    (∃ r ∈ T, r * Fr.zf i = Fr.zf j * r ∧ r * Fr.zf j = Fr.zf i * r) ∧
    (∀ g : G, conjSub g (Mf Fr i j) = Mf Fr i j → (∀ t ∈ T, g * t = t * g) →
      g * (Fr.zf i * Fr.zf j) = (Fr.zf i * Fr.zf j) * g → Odd (orderOf g) →
      g * Fr.zf i = Fr.zf i * g) := by
  subst hi hj
  obtain ⟨ψ, hψ, hrange, hlong, hTψ⟩ := LF.exists_chart S hT hA
  have hl0 := hlong 0
  have hl1 := hlong 1
  have hmulψ : ψ (longInv (GaloisField p f) 2 0 * longInv (GaloisField p f) 2 1) =
      Fr.zf (l.succAbove 0) * Fr.zf (l.succAbove 1) := by rw [map_mul, hl0, hl1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hTψ]
    exact nonempty_equiv_node ψ hψ
  · rw [← hmulψ, hTψ]
    exact Subgroup.mem_map_of_mem ψ LeviModel.neg_one_mem_range_shortBlock
  · refine ⟨ψ (shortBlock (GaloisField p f) fin_two_zero_ne_one (weylMat (GaloisField p f))), ?_,
      ?_, ?_⟩
    · rw [hTψ]
      exact Subgroup.mem_map_of_mem ψ ⟨_, rfl⟩
    · rw [← hl0, ← hl1, ← map_mul, ← map_mul,
        LeviModel.shortBlock_weyl_mul_longInv_zero]
    · rw [← hl0, ← hl1, ← map_mul, ← map_mul,
        LeviModel.shortBlock_weyl_mul_longInv_one]
  · intro g hMg hcT hcz hog
    have hodd : ringChar (GaloisField p f) ≠ 2 :=
      ringChar_ne_two_of_two_ne_zero' S.two_ne_zero
    refine hl0 ▸ commute_longInv_of_centralizes_node hodd S.four_le ψ hψ ?_ ?_ ?_ ?_ hog
    · intro x
      rw [hrange, ← hMg]
      exact conj_mem_conjSub (hrange ▸ ⟨x, rfl⟩)
    · intro x
      have hx : ψ x ∈ conjSub g (Mf Fr (l.succAbove 0) (l.succAbove 1)) := by
        rw [hMg, ← hrange]
        exact ⟨x, rfl⟩
      rw [hrange]
      exact mem_conjSub_iff.mp hx
    · intro B
      apply hcT
      rw [hTψ]
      exact Subgroup.mem_map_of_mem ψ ⟨B, rfl⟩
    · rw [hmulψ]
      exact hcz

theorem oddCore_levi_le_center (S : CSetupW p f 2 Ω K z) (hconn : DeltaConnected Ω)
    (hZ : Subgroup.center G = ⊥) (Fr : Frame p f 2 Ω K z) {x₀ x₁ x₂ : G}
    (hx₀ : x₀ ∈ Fr.Tf 0) (hx₁ : x₁ ∈ Fr.Tf 1) (hx₂ : x₂ ∈ Fr.Tf 2)
    (hn01 : ¬ Mf Fr 0 1 ≤ Subgroup.centralizer ({x₀ * x₁} : Set G))
    (hz01 : ¬ (Mf Fr 0 1 ⊓ Subgroup.centralizer ({x₀ * x₁} : Set G) ≤
      Subgroup.centralizer ({Fr.zf 0} : Set G)))
    (hn12 : ¬ Mf Fr 1 2 ≤ Subgroup.centralizer ({x₁ * x₂} : Set G))
    (hz12 : ¬ (Mf Fr 1 2 ⊓ Subgroup.centralizer ({x₁ * x₂} : Set G) ≤
      Subgroup.centralizer ({Fr.zf 1} : Set G))) :
    classicalInvolutionOddCore ↥(leviNode (Mf Fr 0 1) (x₀ * x₁) ⊔ leviNode (Mf Fr 1 2) (x₁ * x₂)) ≤
      Subgroup.center ↥(leviNode (Mf Fr 0 1) (x₀ * x₁) ⊔ leviNode (Mf Fr 1 2) (x₁ * x₂)) := by
  classical
  have hodd : Odd (Nat.card (GaloisField p f)) := S.odd_card
  have h3 : 3 ≤ Nat.card (GaloisField p f) := by have := S.four_le; omega
  have hsq : ∀ i : Fin 3, Fr.zf i * Fr.zf i = 1 := fun i => by
    have h := pow_orderOf_eq_one (Fr.zf i)
    rw [(Fr.clsW S i).orderOf_eq_two, pow_two] at h
    exact h
  have hcomm : ∀ i j : Fin 3, Fr.zf i * Fr.zf j = Fr.zf j * Fr.zf i := fun i j => Fr.zf_commW S i j
  have htrip := zf_mul_zf_mul_zf S hconn hZ Fr
  have hz2 : Fr.zf 2 = Fr.zf 0 * Fr.zf 1 := by
    have h1 : Fr.zf 0 * Fr.zf 1 * Fr.zf 2 = 1 := htrip
    calc Fr.zf 2 = (Fr.zf 0 * Fr.zf 1) * (Fr.zf 0 * Fr.zf 1) * Fr.zf 2 := by
          rw [show (Fr.zf 0 * Fr.zf 1) * (Fr.zf 0 * Fr.zf 1) = 1 by
            rw [mul_assoc, ← mul_assoc (Fr.zf 1), ← hcomm 0 1, mul_assoc, hsq 1, mul_one, hsq 0],
            one_mul]
      _ = Fr.zf 0 * Fr.zf 1 := by rw [mul_assoc, h1, mul_one]
  have hz0 : Fr.zf 0 = Fr.zf 1 * Fr.zf 2 := by
    have h1 : Fr.zf 0 * (Fr.zf 1 * Fr.zf 2) = 1 := by rw [← mul_assoc]; exact htrip
    calc Fr.zf 0 = Fr.zf 0 * ((Fr.zf 1 * Fr.zf 2) * (Fr.zf 1 * Fr.zf 2)) := by
          rw [show (Fr.zf 1 * Fr.zf 2) * (Fr.zf 1 * Fr.zf 2) = 1 by
            rw [mul_assoc, ← mul_assoc (Fr.zf 2), ← hcomm 1 2, mul_assoc, hsq 2, mul_one, hsq 1],
            mul_one]
      _ = Fr.zf 1 * Fr.zf 2 := by rw [← mul_assoc, h1, one_mul]
  have hz20 : Fr.zf 2 * Fr.zf 0 = Fr.zf 1 := by
    rw [hz2, mul_assoc, ← hcomm 0 1, ← mul_assoc, hsq 0, one_mul]
  set T₀ := leviNode (Mf Fr 0 1) (x₀ * x₁) with hT₀
  set T₁ := leviNode (Mf Fr 1 2) (x₁ * x₂) with hT₁
  set Y := T₀ ⊔ T₁ with hY
  have hx₀K : x₀ ∈ Fr.Kf 0 := Frame.Tf_le 0 hx₀
  have hx₁K : x₁ ∈ Fr.Kf 1 := Frame.Tf_le 1 hx₁
  have hx₂K : x₂ ∈ Fr.Kf 2 := Frame.Tf_le 2 hx₂
  have hd₀ : x₀ * x₁ ∈ Mf Fr 0 1 := (Mf Fr 0 1).mul_mem
    (Tf_le_Mf Fr 0 (Or.inl rfl) hx₀) (Tf_le_Mf Fr 1 (Or.inr rfl) hx₁)
  have hd₁ : x₁ * x₂ ∈ Mf Fr 1 2 := (Mf Fr 1 2).mul_mem
    (Tf_le_Mf Fr 1 (Or.inl rfl) hx₁) (Tf_le_Mf Fr 2 (Or.inr rfl) hx₂)
  have hk₂ : ∀ m ∈ Mf Fr 0 1, m * x₂ = x₂ * m := fun m hm =>
    commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) m hm x₂ hx₂K
  have hk₀ : ∀ m ∈ Mf Fr 1 2, m * x₀ = x₀ * m := fun m hm =>
    commutes_Mf_Kf Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide) m hm x₀ hx₀K
  have hx₀x₁ : x₀ * x₁ = x₁ * x₀ := Fr.commute 0 1 (by decide) x₀ hx₀K x₁ hx₁K
  have hx₀x₂ : x₀ * x₂ = x₂ * x₀ := Fr.commute 0 2 (by decide) x₀ hx₀K x₂ hx₂K
  have hh' : x₀ * x₁ * x₂ = x₁ * x₂ * x₀ := by
    rw [hx₀x₁, mul_assoc, hx₀x₂, ← mul_assoc]
  have hT₀M : T₀ ≤ Mf Fr 0 1 := leviNode_le _ _
  have hT₁M : T₁ ≤ Mf Fr 1 2 := leviNode_le _ _
  have hA₀ : IsAdaptedShortIn (Mf Fr 0 1) (Fr.Tf 0) (Fr.Tf 1) (Fr.zf 0) T₀ :=
    ⟨x₀, hx₀, x₁, hx₁, hn01, hz01, rfl⟩
  have hA₁ : IsAdaptedShortIn (Mf Fr 1 2) (Fr.Tf 1) (Fr.Tf 2) (Fr.zf 1) T₁ :=
    ⟨x₁, hx₁, x₂, hx₂, hn12, hz12, rfl⟩
  obtain ⟨LF₂⟩ := exists_localFrameIW S Fr 2
  obtain ⟨LF₀⟩ := exists_localFrameIW S Fr 0
  obtain ⟨⟨e₀⟩, hzz₀, ⟨r₀, hr₀T, hr₀a, -⟩, hB₀⟩ :=
    node_facts S Fr LF₂ (by decide) (by decide) hT₀M hA₀
  obtain ⟨⟨e₁⟩, hzz₁, ⟨r₁, hr₁T, hr₁a, -⟩, hB₁⟩ :=
    node_facts S Fr LF₀ (by decide) (by decide) hT₁M hA₁
  have hz2T₀ : Fr.zf 2 ∈ T₀ := by rw [hz2]; exact hzz₀
  have hz0T₁ : Fr.zf 0 ∈ T₁ := by rw [hz0]; exact hzz₁
  have hT₀Y : T₀ ≤ Y := le_sup_left
  have hT₁Y : T₁ ≤ Y := le_sup_right
  have hYh : ∀ y ∈ Y, y * (x₀ * x₁ * x₂) = (x₀ * x₁ * x₂) * y := by
    have h0 : ∀ t ∈ T₀, t * (x₀ * x₁ * x₂) = (x₀ * x₁ * x₂) * t := by
      intro t ht
      have h1 : t * (x₀ * x₁) = (x₀ * x₁) * t :=
        Subgroup.mem_centralizer_singleton_iff.mp (leviNode_le_centralizer _ _ ht)
      have h2 : t * x₂ = x₂ * t := hk₂ t (hT₀M ht)
      exact ((show Commute t (x₀ * x₁) from h1).mul_right (show Commute t x₂ from h2)).eq
    have h1' : ∀ t ∈ T₁, t * (x₀ * x₁ * x₂) = (x₀ * x₁ * x₂) * t := by
      intro t ht
      rw [hh']
      have h1 : t * (x₁ * x₂) = (x₁ * x₂) * t :=
        Subgroup.mem_centralizer_singleton_iff.mp (leviNode_le_centralizer _ _ ht)
      have h2 : t * x₀ = x₀ * t := hk₀ t (hT₁M ht)
      exact ((show Commute t (x₁ * x₂) from h1).mul_right (show Commute t x₀ from h2)).eq
    have hY' : Y ≤ Subgroup.centralizer ({x₀ * x₁ * x₂} : Set G) :=
      sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (h0 t ht))
        (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (h1' t ht))
    exact fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hY' hy)
  set N₀ : Subgroup G := (classicalInvolutionOddCore ↥Y).map Y.subtype with hN₀
  have hN₀Y : N₀ ≤ Y := Subgroup.map_subtype_le _
  have hN₀norm : ∀ y ∈ Y, ∀ n ∈ N₀, y * n * y⁻¹ ∈ N₀ := by
    rintro y hy _ ⟨n, hn, rfl⟩
    exact ⟨⟨y, hy⟩ * n * ⟨y, hy⟩⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : (classicalInvolutionOddCore ↥Y).Normal) n hn
        ⟨y, hy⟩, rfl⟩
  have hN₀odd : Odd (Nat.card N₀) := by
    rw [hN₀, Subgroup.card_map_of_injective Y.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hC2 : ∀ g ∈ N₀, g * Fr.zf 2 = Fr.zf 2 * g → ∀ y ∈ Y, g * y = y * g := by
    intro g hgN hgz2 y hy
    have hgY : g ∈ Y := hN₀Y hgN
    have hgh : g * (x₀ * x₁ * x₂) = (x₀ * x₁ * x₂) * g := hYh g hgY
    have hgh' : g * (x₀ * x₁ * x₂) * g⁻¹ = x₀ * x₁ * x₂ := mul_inv_eq_iff_eq_mul.mpr hgh
    have hMg : conjSub g (Mf Fr 0 1) = Mf Fr 0 1 :=
      conjSub_Mf_eq_of_commute S Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide)
        (by decide) hgz2
    have hT₀g : conjSub g T₀ = T₀ := conjSub_leviNode hd₀ hk₂ hMg hgh'
    have hgT₀ : ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀ := fun t ht => by
      have := conj_mem_conjSub (n := g) ht
      rwa [hT₀g] at this
    have hcT₀ : ∀ t ∈ T₀, g * t = t * g :=
      commute_of_mem_oddNormal hodd h3 e₀.symm hN₀odd hT₀Y hN₀norm hgN hgT₀
    have hord : Odd (orderOf g) := hN₀odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hgN)
    have hgz0 : g * Fr.zf 0 = Fr.zf 0 * g :=
      hB₀ g hMg hcT₀ (by rw [← hz2]; exact hgz2) hord
    have hMg' : conjSub g (Mf Fr 1 2) = Mf Fr 1 2 :=
      conjSub_Mf_eq_of_commute S Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide)
        (by decide) hgz0
    have hgh'' : g * (x₁ * x₂ * x₀) * g⁻¹ = x₁ * x₂ * x₀ := by rw [← hh']; exact hgh'
    have hT₁g : conjSub g T₁ = T₁ := conjSub_leviNode hd₁ hk₀ hMg' hgh''
    have hgT₁ : ∀ t ∈ T₁, g * t * g⁻¹ ∈ T₁ := fun t ht => by
      have := conj_mem_conjSub (n := g) ht
      rwa [hT₁g] at this
    have hcT₁ : ∀ t ∈ T₁, g * t = t * g :=
      commute_of_mem_oddNormal hodd h3 e₁.symm hN₀odd hT₁Y hN₀norm hgN hgT₁
    have hY' : Y ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hcT₀ t ht).symm)
        (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hcT₁ t ht).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hY' hy)).symm
  have hC1 : ∀ g ∈ N₀, g * Fr.zf 1 = Fr.zf 1 * g → ∀ y ∈ Y, g * y = y * g := by
    intro g hgN hgz1 y hy
    have hr₁Y : r₁ ∈ Y := hT₁Y hr₁T
    have hg' : r₁ * g * r₁⁻¹ ∈ N₀ := hN₀norm r₁ hr₁Y g hgN
    have hz2eq : r₁ * Fr.zf 1 * r₁⁻¹ = Fr.zf 2 := mul_inv_eq_iff_eq_mul.mpr hr₁a
    have hc : (r₁ * g * r₁⁻¹) * Fr.zf 2 = Fr.zf 2 * (r₁ * g * r₁⁻¹) := by
      rw [← hz2eq]
      calc r₁ * g * r₁⁻¹ * (r₁ * Fr.zf 1 * r₁⁻¹) = r₁ * (g * Fr.zf 1) * r₁⁻¹ := by group
        _ = r₁ * (Fr.zf 1 * g) * r₁⁻¹ := by rw [hgz1]
        _ = r₁ * Fr.zf 1 * r₁⁻¹ * (r₁ * g * r₁⁻¹) := by group
    have key := hC2 _ hg' hc (r₁ * y * r₁⁻¹) (Y.mul_mem (Y.mul_mem hr₁Y hy) (Y.inv_mem hr₁Y))
    have h2 : r₁ * (g * y) * r₁⁻¹ = r₁ * (y * g) * r₁⁻¹ := by
      calc r₁ * (g * y) * r₁⁻¹ = r₁ * g * r₁⁻¹ * (r₁ * y * r₁⁻¹) := by group
        _ = r₁ * y * r₁⁻¹ * (r₁ * g * r₁⁻¹) := key
        _ = r₁ * (y * g) * r₁⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hC0 : ∀ g ∈ N₀, g * Fr.zf 0 = Fr.zf 0 * g → ∀ y ∈ Y, g * y = y * g := by
    intro g hgN hgz0 y hy
    have hr₀Y : r₀ ∈ Y := hT₀Y hr₀T
    have hg' : r₀ * g * r₀⁻¹ ∈ N₀ := hN₀norm r₀ hr₀Y g hgN
    have hz1eq : r₀ * Fr.zf 0 * r₀⁻¹ = Fr.zf 1 := mul_inv_eq_iff_eq_mul.mpr hr₀a
    have hc : (r₀ * g * r₀⁻¹) * Fr.zf 1 = Fr.zf 1 * (r₀ * g * r₀⁻¹) := by
      rw [← hz1eq]
      calc r₀ * g * r₀⁻¹ * (r₀ * Fr.zf 0 * r₀⁻¹) = r₀ * (g * Fr.zf 0) * r₀⁻¹ := by group
        _ = r₀ * (Fr.zf 0 * g) * r₀⁻¹ := by rw [hgz0]
        _ = r₀ * Fr.zf 0 * r₀⁻¹ * (r₀ * g * r₀⁻¹) := by group
    have key := hC1 _ hg' hc (r₀ * y * r₀⁻¹) (Y.mul_mem (Y.mul_mem hr₀Y hy) (Y.inv_mem hr₀Y))
    have h2 : r₀ * (g * y) * r₀⁻¹ = r₀ * (y * g) * r₀⁻¹ := by
      calc r₀ * (g * y) * r₀⁻¹ = r₀ * g * r₀⁻¹ * (r₀ * y * r₀⁻¹) := by group
        _ = r₀ * y * r₀⁻¹ * (r₀ * g * r₀⁻¹) := key
        _ = r₀ * (y * g) * r₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hne1 : ∀ i : Fin 3, Fr.zf i ≠ 1 := fun i h => by
    have := (Fr.clsW S i).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hVk := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions (Fr.zf 2)
    (Fr.zf 0) (hsq 2) (hsq 0) (hne1 2) (hne1 0) (zf_ne_of_ne S Fr (by decide))
    (hcomm 2 0 : Commute (Fr.zf 2) (Fr.zf 0))
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (Fr.zf 2) (Fr.zf 0) (hsq 2)
    (hsq 0) (hcomm 2 0 : Commute (Fr.zf 2) (Fr.zf 0)) with hV
  have hVY : V ≤ Y := by
    intro x hx
    change x ∈ ({Fr.zf 2 * Fr.zf 0, Fr.zf 2, Fr.zf 0, 1} : Set G) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Y.mul_mem (hT₀Y hz2T₀) (hT₁Y hz0T₁)
    · exact hT₀Y hz2T₀
    · exact hT₁Y hz0T₁
    · exact Y.one_mem
  have hloc : ∀ v ∈ V, v ≠ 1 → ∀ g ∈ N₀, g * v = v * g → ∀ y ∈ Y, g * y = y * g := by
    intro v hv hv1 g hg hgv y hy
    change v ∈ ({Fr.zf 2 * Fr.zf 0, Fr.zf 2, Fr.zf 0, 1} : Set G) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [hz20] at hgv
      exact hC1 g hg hgv y hy
    · exact hC2 g hg hgv y hy
    · exact hC0 g hg hgv y hy
    · exact absurd rfl hv1
  have hall := oddNormal_commute_of_klein hN₀norm hN₀odd hVY hVk hloc
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (hall (n : G) ⟨n, hn, rfl⟩ (y : G) y.2).symm

end Frame

end CFSG.ClassicalInvolution.RouteD
