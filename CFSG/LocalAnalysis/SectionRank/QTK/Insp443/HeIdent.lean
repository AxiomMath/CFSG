module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HeLat
public import CFSG.Quasithin.Vol2.KGFactC31HeSx

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.He CFSG.SectionRank.QTK.Insp443.He CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

variable {A : Type} [Group A] [Finite A] {L V MK : Subgroup A}
  {ι : A →* Equiv.Perm (Fin 8330)}

namespace He

omit [Finite A] in
theorem Emb.normalizer_comap (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    {X : Subgroup (Equiv.Perm (Fin 8330))} (hX : X ≤ heP) :
    Subgroup.normalizer ((X.comap ι : Subgroup A) : Set A) =
      (heP ⊓ Subgroup.normalizer (X : Set (Equiv.Perm (Fin 8330)))).comap ι := by
  refine le_antisymm ?_ ?_
  · intro x hx
    refine Subgroup.mem_comap.mpr
      ⟨hι.mem_heP (Subgroup.mem_top x), Subgroup.mem_normalizer_iff.mpr fun z => ?_⟩
    by_cases hz : z ∈ heP
    · obtain ⟨a, -, rfl⟩ := hι.exists_of_mem hz
      have h := Subgroup.mem_normalizer_iff.mp hx a
      simpa only [Subgroup.mem_comap, map_mul, map_inv] using h
    · have hzX : z ∉ X := fun h => hz (hX h)
      have hz' : ι x * z * (ι x)⁻¹ ∉ X := by
        intro h
        apply hz
        have hxP := hι.mem_heP (Subgroup.mem_top x)
        have hmem : ι x * z * (ι x)⁻¹ ∈ heP := hX h
        have hthis : (ι x)⁻¹ * (ι x * z * (ι x)⁻¹) * (ι x) ∈ heP :=
          heP.mul_mem (heP.mul_mem (heP.inv_mem hxP) hmem) hxP
        have hz_eq : (ι x)⁻¹ * (ι x * z * (ι x)⁻¹) * (ι x) = z := by group
        rwa [hz_eq] at hthis
      exact ⟨fun h => absurd h hzX, fun h => absurd h hz'⟩
  · intro x hx
    have hx' := Subgroup.mem_comap.mp hx
    refine Subgroup.mem_normalizer_iff.mpr fun a => ?_
    have h := Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hx').2 (ι a)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using h

omit [Finite A] in
theorem Emb.card_pCoreOf_comap (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    {Y : Subgroup (Equiv.Perm (Fin 8330))} (hY : Y ≤ heP) :
    Nat.card ↥(pCoreOf 2 (Y.comap ι)) = Nat.card ↥(pCoreOf 2 Y) := by
  have hcard : ∀ H : Subgroup A, Nat.card ↥(pCoreOf 2 H) = Nat.card (CFSG.pCore 2 ↥H) := by
    intro H
    rw [pCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  have hcardY : Nat.card ↥(pCoreOf 2 Y) = Nat.card (CFSG.pCore 2 ↥Y) := by
    rw [pCoreOf, Subgroup.card_map_of_injective Y.subtype_injective]
  rw [hcard (Y.comap ι), hcardY]
  let e : ↥(Y.comap ι) ≃* ↥Y :=
    (Subgroup.equivMapOfInjective (Y.comap ι) ι hι.inj).trans
      (MulEquiv.subgroupCongr (hι.map_comap hY))
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e,
    Subgroup.card_map_of_injective e.injective]

end He

omit [Finite A] in
theorem KConfig.cent_eq_of_ref (h : KConfig A L V MK) (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    {k l : ℕ} {v : Fin k → Equiv.Perm (Fin 8330)} {u : Fin l → Equiv.Perm (Fin 8330)}
    (hu : EBasis u) (hcent : ∀ x ∈ heAutGroup, (∀ i, x * v i = v i * x) → x ∈ eSub hu)
    (hvV : ∀ i, v i ∈ V.map ι) :
    Subgroup.centralizer (V : Set A) = (eSub hu).comap ι := by
  have hle : Subgroup.centralizer (V : Set A) ≤ (eSub hu).comap ι := by
    intro x hx
    refine hcent _ (hι.mem_heAutGroup x) fun i => ?_
    obtain ⟨v', hv', hvi⟩ := hvV i
    rw [← hvi, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx v' hv']
  refine le_antisymm hle fun z hz => Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_
  have hv'E := hle (h.le_centralizer hv')
  apply hι.inj
  rw [map_mul, map_mul]
  exact eSub_comm hu _ _ hv'E hz

private theorem prime_eq_seven {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 21504) : p = 7 := by
  have h' : p ∣ 2 ^ 10 * 3 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) h2; omega
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1

theorem KConfig.he_not_w7
    (h : KConfig A L V MK) (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    (hW : ∀ i, vW7 i ∈ V.map ι) {y : A} (hy : y ∈ L) {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hyk : y ^ p ^ k = 1) (hy1 : y ≠ 1) : False := by
  have hC := h.cent_eq_of_ref hι basis_Q (fun x hx hc => mem_Q_of_cent hx hc) hW
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    rw [hC]
    exact IsPGroup.of_card (n := 4) (by rw [hι.card_comap Q_le_heP, card_eSub])
  set N : Subgroup A := (heP ⊓ eNorm basis_Q).comap ι with hNdef
  have hN : Subgroup.normalizer (Subgroup.centralizer (V : Set A) : Set A) = N := by
    rw [hC, hNdef]
    exact He.Emb.normalizer_comap hι Q_le_heP
  have hNc : Nat.card ↥N = 21504 := by
    rw [hNdef, hι.card_comap (Y := heP ⊓ eNorm basis_Q) inf_le_left, heP_inf_eNorm_Q, card_N7]
  have hLN : L ≤ N := by
    rw [← hN]
    exact h.le_normalizer_centralizer
  have hNL : N ≤ Subgroup.normalizer (L : Set A) := by
    rw [← hN]
    exact h.normalizer_centralizer_le h2
  have hp7 : p = 7 := by
    obtain ⟨j, hj, hoy⟩ := exists_orderOf_eq_pow hp hyk hy1
    have h1 : orderOf y ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨y, hLN hy⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hoy, hNc] at h1
    exact prime_eq_seven hp hp5 ((dvd_pow_self p hj.ne').trans h1)
  rw [hp7] at hyk
  obtain ⟨a, -, hay⟩ := hι.exists_of_mem (x7_mem |>.1)
  have haN : a ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hay]
    exact x7_mem
  have hoa : orderOf a = 7 := by
    rw [← orderOf_injective ι hι.inj, hay, orderOf_x7]
  have hNp : ¬ 7 ^ 2 ∣ Nat.card N := by rw [hNc]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have haL : a ∈ L := M24.mem_of_sylow haN hoa hNp hLN hNL hy ⟨k, hyk⟩ hy1
  obtain ⟨b, -, hb⟩ := hι.exists_of_mem (c7_mem |>.1)
  have hbN : b ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hb]
    exact c7_mem
  have hbaL : b * a * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hNL hbN) a).mp haL
  have hL7 : chainL7.originalSubgroup ≤ L.map ι := by
    rw [L7_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [l7GenW, List.mem_cons, List.not_mem_nil, List.mem_singleton, or_false] at hw
    rcases hw with hw | hw
    · rw [hw, ← hay]
      exact Subgroup.mem_map_of_mem ι haL
    · rw [hw, elt_l7Gen]
      have h : ι (b * a * b⁻¹) = elt c7W * elt x7W * (elt c7W)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hb, hay]
      rw [← h]
      exact Subgroup.mem_map_of_mem ι hbaL
  have hLsL : chainL7.originalSubgroup.comap ι ≤ L := by
    have h := Subgroup.comap_mono (f := ι) hL7
    rwa [Subgroup.comap_map_eq_self_of_injective hι.inj] at h
  have hLeq : L = n7Grp.comap ι := by
    refine le_antisymm ?_ ?_
    · rw [← heP_inf_eNorm_Q, ← hNdef]
      exact hLN
    · rw [← L7_eq_N7]
      exact hLsL
  have hO2 : Nat.card ↥(pCoreOf 2 L) = 128 := by
    rw [hLeq, He.Emb.card_pCoreOf_comap hι (Y := n7Grp)
      (N7_le.trans inf_le_left), card_pCoreOf_N7]
  have hsub : pCoreOf 2 L ≤ (eSub basis_Q).comap ι := hC ▸ h.pCoreOf_le
  have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
    (Subgroup.inclusion_injective hsub)
  rw [hO2, hι.card_comap Q_le_heP, card_eSub] at hle
  norm_num at hle

theorem KConfig.he_eq_w5
    (h : KConfig A L V MK) (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι)
    (hW : ∀ i, vW5 i ∈ V.map ι) {y : A} (hy : y ∈ L) {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hyk : y ^ p ^ k = 1) (hy1 : y ≠ 1) :
    L = lGrp.comap ι ∧ V ≤ (eSub basis_E).comap ι := by
  have hC := h.cent_eq_of_ref hι basis_E (fun x hx hc => mem_E_of_cent hx hc) hW
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    rw [hC]
    exact IsPGroup.of_card (n := 6) (by rw [hι.card_comap E_le_heP, card_eSub])
  set N : Subgroup A := (heP ⊓ eNorm basis_E).comap ι with hNdef
  have hN : Subgroup.normalizer (Subgroup.centralizer (V : Set A) : Set A) = N := by
    rw [hC, hNdef]
    exact He.Emb.normalizer_comap hι E_le_heP
  have hNc : Nat.card ↥N = 138240 := by
    rw [hNdef, hι.card_comap (Y := heP ⊓ eNorm basis_E) inf_le_left, heP_inf_eNorm_E, card_Ns]
  have hLN : L ≤ N := by
    rw [← hN]
    exact h.le_normalizer_centralizer
  have hNL : N ≤ Subgroup.normalizer (L : Set A) := by
    rw [← hN]
    exact h.normalizer_centralizer_le h2
  have hp5' : p = 5 := by
    obtain ⟨j, hj, hoy⟩ := exists_orderOf_eq_pow hp hyk hy1
    have h1 : orderOf y ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨y, hLN hy⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hoy, hNc] at h1
    exact prime_eq_five hp hp5 ((dvd_pow_self p hj.ne').trans h1)
  subst hp5'
  have hLsP : lGrp ≤ heP := Ls_le.trans inf_le_left
  have hLsN : lGrp.comap ι ≤ N := by
    rw [hNdef]
    exact Subgroup.comap_mono Ls_le
  have hi : (lGrp.comap ι).relIndex N ≤ 4 := by
    have h1 := (lGrp.comap ι).relIndex_mul_card (K := N)
    rw [inf_eq_left.mpr hLsN, hNc, hι.card_comap hLsP, card_Ls] at h1
    omega
  have hL_le : L ≤ lGrp.comap ι :=
    le_of_perfect_of_relIndex_le hLN h.perfect hi
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, -, hay⟩ := hι.exists_of_mem (hLsP y5_mem_Ls)
  have haN : a ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hay]
    exact Ls_le y5_mem_Ls
  have hoa : orderOf a = 5 := by
    rw [← orderOf_injective ι hι.inj, hay, orderOf_y5]
  have hNp : ¬ 5 ^ 2 ∣ Nat.card N := by rw [hNc]; norm_num
  have haL : a ∈ L := M24.mem_of_sylow haN hoa hNp hLN hNL hy ⟨k, hyk⟩ hy1
  have hLsM : lGrp ≤ L.map ι := by
    rw [Ls_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    rcases mem_lsGenW hw with rfl | ⟨n, hn, rfl⟩
    · rw [← hay]
      exact Subgroup.mem_map_of_mem ι haL
    · obtain ⟨b, -, hb⟩ := hι.exists_of_mem
        (elt_mem_heP (List.all_eq_true.1 letters_njW n hn))
      have hbN : b ∈ N := by
        rw [hNdef, Subgroup.mem_comap, hb]
        exact ⟨elt_mem_heP (List.all_eq_true.1 letters_njW n hn), nj_mem_eNorm hn⟩
      have hba : b * a * b⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hNL hbN) a).mp haL
      have h : ι (b * a * b⁻¹) = elt (n ++ y5W ++ invW n) := by
        rw [map_mul, map_mul, map_inv, hb, hay, elt_lsGen hn]
      rw [← h]
      exact Subgroup.mem_map_of_mem ι hba
  refine ⟨le_antisymm hL_le ?_, hC ▸ h.le_centralizer⟩
  have h := Subgroup.comap_mono (f := ι) hLsM
  rwa [Subgroup.comap_map_eq_self_of_injective hι.inj] at h

end CFSG.SectionRank.QTK.Insp443

end
