module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineTheta
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem isSylowOf_sup_odd' {P O : Subgroup X} (hP : IsPGroup 2 P) (hO : Odd (Nat.card O))
    (hPO : P ≤ Subgroup.normalizer (O : Set X)) (hinf : P ⊓ O = ⊥) : IsSylowOf 2 P (P ⊔ O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  refine ⟨le_sup_left, hP, ?_⟩
  have hcard : Nat.card (P ⊔ O : Subgroup X) = Nat.card P * Nat.card O := by
    rw [sup_comm, card_sup_of_le_normalizer hPO (by rw [inf_comm]; exact hinf), mul_comm]
  have hrel := Subgroup.relIndex_mul_card P (P ⊔ O)
  rw [inf_eq_left.mpr le_sup_left, hcard] at hrel
  have hrelN : P.relIndex (P ⊔ O) = Nat.card O := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [mul_comm (Nat.card P)] at hrel
    exact Nat.eq_of_mul_eq_mul_right hpos hrel
  rw [hrelN]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)

omit [Finite X] in
theorem card_map_eq_of_ker {Y : Type*} [Group Y] (f : X →* Y) {K : Subgroup X}
    (hK : ∀ x ∈ K, f x = 1 → x = 1) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hK x x.2 hx)
  calc Nat.card (K.map f) = Nat.card ((⊤ : Subgroup K).map (f.comp K.subtype)) := by
        rw [← Subgroup.map_map, map_subtype_top]
    _ = Nat.card (⊤ : Subgroup K) := Subgroup.card_map_of_injective hinj
    _ = Nat.card K := Subgroup.card_top

theorem pRank_map_eq_of_ker {Y : Type*} [Group Y] [Finite Y] (f : X →* Y) {K : Subgroup X}
    (hK : ∀ x ∈ K, f x = 1 → x = 1) : pRank 2 (K.map f) = pRank 2 K := by
  apply le_antisymm
  · obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two (K.map f)
    set E' := E.comap f ⊓ K
    have hE'map : E'.map f = E := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hEK hy
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    have hK' : ∀ x ∈ E', f x = 1 → x = 1 := fun x hx => hK x hx.2
    have hcard' : Nat.card E' = Nat.card E := by
      rw [← hE'map, card_map_eq_of_ker f hK']
    have hinj : ∀ a ∈ E', ∀ b ∈ E', f a = f b → a = b := by
      intro a ha b hb hab
      have := hK' (a * b⁻¹) (E'.mul_mem ha (E'.inv_mem hb)) (by rw [map_mul, map_inv, hab,
        mul_inv_cancel])
      exact mul_inv_eq_one.mp this
    refine CFSG.SectionRank.le_pRank one_lt_two (E := E') inf_le_right ⟨⟨⟨fun a b => ?_⟩⟩,
      fun x hx => ?_⟩ (hcard'.trans hcard)
    · apply Subtype.ext
      apply hinj _ (E'.mul_mem a.2 b.2) _ (E'.mul_mem b.2 a.2)
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2.1⟩ ⟨f b, b.2.1⟩)
    · apply hinj _ (E'.pow_mem hx 2) _ E'.one_mem
      rw [map_pow, hE.2 _ hx.1, map_one]
  · obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two K
    refine CFSG.SectionRank.le_pRank one_lt_two (Subgroup.map_mono hEK)
      (CFSG.SectionRank.isElemAbelian_map hE f) ?_
    rw [card_map_eq_of_ker f fun x hx => hK x (hEK hx), hcard]

namespace Core49

variable {A T S Q H : Subgroup X}

theorem center_two (c : Core49 A T S Q H) {z : X} (hz : z ∈ centerOf A) :
    ∃ k : ℕ, z ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  set w := z ^ (2 ^ k)
  have hwA : w ∈ A := A.pow_mem hz.1 _
  have hwm : orderOf w = m := by
    rw [orderOf_pow' z (by positivity), hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
      (by positivity)]
  set W : Subgroup A := Subgroup.zpowers ⟨w, hwA⟩
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : g * ⟨w, hwA⟩ = ⟨w, hwA⟩ * g := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hz.2 (2 ^ k)) g g.2
      exact this
    rw [(Commute.zpow_right hcomm j).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ j
  have hWodd : Odd (Nat.card W) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hwm]
    exact hm
  have hWle : W ≤ CFSG.oddCore A := le_sSup ⟨hWn, hWodd⟩
  rw [c.oddCore, le_bot_iff] at hWle
  have : (⟨w, hwA⟩ : A) ∈ W := Subgroup.mem_zpowers _
  rw [hWle, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

end Core49

omit [Finite X] in
theorem mk_mem_map_iff {K N : Subgroup X} [N.Normal] {z : X} :
    QuotientGroup.mk' N z ∈ K.map (QuotientGroup.mk' N) ↔ z ∈ K ⊔ N := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

namespace Core49

variable {A T S Q H : Subgroup X} {N : Subgroup X} [N.Normal]

theorem sup_quotient (c : Core49 A T S Q H) :
    A.map (QuotientGroup.mk' N) ⊔ T.map (QuotientGroup.mk' N) = ⊤ := by
  rw [← Subgroup.map_sup, c.top, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem frame_quotient (c : Core49 A T S Q H) (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
    Frame (A.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) :=
  c.frame.map N (by rw [hN]; exact inf_le_left.trans inf_le_right)

theorem mk_eq_one (c : Core49 A T S Q H) (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X))
    {t : X} (ht : t ∈ T) (h1 : QuotientGroup.mk' N t = 1) : t = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN] at h1
  have hmem : t ∈ T ⊓ A := ⟨ht, h1.1.2⟩
  rwa [c.frame.inf_eq_bot, Subgroup.mem_bot] at hmem

theorem hyp43_quotient (c : Core49 A T S Q H) (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
    Hyp43 (A.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N))
      ((thetaCore A T ⊔ T ⊔ N).map (QuotientGroup.mk' N))
      (Subgroup.normalizer (((thetaCore A T ⊔ T ⊔ N).map (QuotientGroup.mk' N) :
        Subgroup (X ⧸ N)) : Set (X ⧸ N))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  refine ⟨Subgroup.le_normalizer, le_rfl, by rw [c.sup_quotient]; exact le_top, ?_, ?_⟩
  ·
    have hTU2 : IsPGroup 2 (T ⊔ N : Subgroup X) := by
      rw [hN]
      exact c.isPGroup_S.to_le (sup_le c.le_S (inf_le_left.trans inf_le_left))
    have hθN : T ⊔ N ≤ Subgroup.normalizer ((thetaCore A T : Subgroup X) : Set X) := by
      refine sup_le (fun t ht => normalizer_gammaJoin_le A T (c.T_le_normalizer_gamma ht)) ?_
      intro u hu
      rw [hN] at hu
      refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
      have h := c.U_central hu x
      rw [← h, mul_inv_cancel_right]
    have hinf : (T ⊔ N) ⊓ thetaCore A T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h2 := hTU2.to_le (inf_le_left : (T ⊔ N) ⊓ thetaCore A T ≤ T ⊔ N)
      have hodd : Odd (Nat.card ((T ⊔ N) ⊓ thetaCore A T : Subgroup X)) :=
        (odd_card_thetaCore A T).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [hk] at hodd
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
      rw [hk0, pow_zero] at hk
      have := Subgroup.card_eq_one.mp hk
      rw [this] at hx
      exact hx
    have hsyl := isSylowOf_sup_odd' hTU2 (odd_card_thetaCore A T) hθN hinf
    have hmap := IsSylowOf.map hsyl π
    have h1 : (T ⊔ N).map π = T.map π := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    rw [h1, sup_comm, ← sup_assoc] at hmap
    exact hmap
  · rintro _ ⟨a, haA, rfl⟩ haH
    by_contra hne
    obtain ⟨⟨x, hxT, hxa⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨t, ht, rfl⟩ := hxT
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hx1 (Subtype.ext (map_one π))
    have hxa' := (mem_rightConjugate_iff _ _ _).mp hxa
    rw [← map_inv, ← map_mul, ← map_mul] at hxa'
    have hat : a * t * a⁻¹ ∈ T ⊔ N := mk_mem_map_iff.mp hxa'
    rw [hN] at hat
    have hK := c.mem_normalizer_of_conj haA ht ht1 hat
    rw [← hN] at hK
    exact haH (Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hK))

theorem card_T_quotient (c : Core49 A T S Q H)
    (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
    Nat.card (T.map (QuotientGroup.mk' N)) = Nat.card T :=
  card_map_eq_of_ker _ fun _ ht h1 => c.mk_eq_one hN ht h1

theorem pRank_quotient (c : Core49 A T S Q H)
    (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
    1 < pRank 2 (T.map (QuotientGroup.mk' N)) := by
  rw [pRank_map_eq_of_ker _ fun _ ht h1 => c.mk_eq_one hN ht h1]
  exact c.pRank_lt

theorem relIndex_quotient_le (c : Core49 A T S Q H)
    (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) {S' : Subgroup (X ⧸ N)}
    (hS' : SylowFrame (A.map (QuotientGroup.mk' N)) (T.map (QuotientGroup.mk' N)) S') :
    (T.map (QuotientGroup.mk' N)).relIndex (S' ⊓ Subgroup.normalizer
      (((thetaCore A T ⊔ T ⊔ N).map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N))) ≤
      Nat.card (T.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N
  set Ab := A.map π
  set Tb := T.map π
  set Hb := Subgroup.normalizer (((thetaCore A T ⊔ T ⊔ N).map π : Subgroup (X ⧸ N)) :
    Set (X ⧸ N))
  have hFb := c.frame_quotient hN
  have h43 := c.hyp43_quotient hN
  have hTb : Tb ≠ ⊥ := by
    intro hbot
    apply c.ne_bot
    rw [eq_bot_iff]
    intro t ht
    have : π t ∈ Tb := Subgroup.mem_map_of_mem π ht
    rw [hbot, Subgroup.mem_bot] at this
    exact c.mk_eq_one hN ht this
  have hTbS : Tb ≤ S' := hS'.le
  have hS2 := hS'.sylow.isPGroup
  have hinf : S' ⊓ Hb = S' ⊓ Subgroup.normalizer (Tb : Set (X ⧸ N)) := by
    apply le_antisymm
    · exact le_inf inf_le_left (h43.le_normalizer_of_le hS2.to_inf_left
        (le_inf hTbS h43.le_H) inf_le_right)
    · exact le_inf inf_le_left ((inf_le_inf_right _ hS'.sylow.le).trans
        (h43.normalizer_le hFb hTb))
  rw [hinf]
  obtain ⟨hdec, hinf2, -⟩ := lemma_4_1 hFb hS'.sylow.le hTbS
  set Pb := S' ⊓ Subgroup.normalizer (Tb : Set (X ⧸ N)) ⊓ Ab with hPbdef
  have hPbN : Pb ≤ Subgroup.normalizer (Tb : Set (X ⧸ N)) := inf_le_left.trans inf_le_right
  have hcardS : Nat.card (S' ⊓ Subgroup.normalizer (Tb : Set (X ⧸ N)) : Subgroup (X ⧸ N)) =
      Nat.card Tb * Nat.card Pb := by
    rw [hdec]
    exact card_sup_of_le_normalizer hPbN hinf2
  set Pt := Pb.comap π ⊓ A with hPtdef
  have hNA : N ≤ A := by rw [hN]; exact inf_le_left.trans inf_le_right
  have hNPt : N ≤ Pt := by
    intro n hn
    refine ⟨?_, hNA hn⟩
    show π n ∈ Pb
    rw [show π n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact Pb.one_mem
  have hPtmap : Pt.map π = Pb := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := hx.2
      exact ⟨a, ⟨hx, ha⟩, rfl⟩
  have hcardPt : Nat.card Pt = Nat.card N * Nat.card Pb := by
    have h1 := Subgroup.card_ker_mul_card_range (π.comp Pt.subtype)
    have hker : (π.comp Pt.subtype).ker = N.subgroupOf Pt := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have hrange : (π.comp Pt.subtype).range = Pb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPtmap]
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNPt).toEquiv] at h1
    exact h1.symm
  have hPt2 : IsPGroup 2 Pt := by
    have hN2 : IsPGroup 2 N := by
      rw [hN]
      exact c.isPGroup_S.to_le (inf_le_left.trans inf_le_left)
    have hPb2 : IsPGroup 2 Pb := hS2.to_le (inf_le_left.trans inf_le_left)
    obtain ⟨a, ha⟩ := hN2.exists_card_eq
    obtain ⟨b, hb⟩ := hPb2.exists_card_eq
    exact IsPGroup.of_card (n := a + b) (by rw [hcardPt, ha, hb, pow_add])
  have hPtN : Pt ≤ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X) := by
    intro y hy
    have hyN : π y ∈ Subgroup.normalizer (Tb : Set (X ⧸ N)) := hPbN hy.1
    have key : ∀ z : X, π z ∈ Subgroup.normalizer (Tb : Set (X ⧸ N)) →
        ∀ k ∈ T ⊔ N, z * k * z⁻¹ ∈ T ⊔ N := by
      intro z hz k hk
      have hk' : π k ∈ Tb := mk_mem_map_iff.mpr hk
      have := (Subgroup.mem_normalizer_iff.mp hz (π k)).mp hk'
      rw [← map_inv, ← map_mul, ← map_mul] at this
      exact mk_mem_map_iff.mp this
    have hyN' : π y⁻¹ ∈ Subgroup.normalizer (Tb : Set (X ⧸ N)) := by
      rw [map_inv]
      exact (Subgroup.normalizer _).inv_mem hyN
    rw [← hN]
    exact mem_normalizer_of_conj_le (key y hyN) (key y⁻¹ hyN')
  have hbound := c.card_le inf_le_right hPtN hPt2
  rw [hcardPt, ← hN, mul_comm (Nat.card T)] at hbound
  have hPb : Nat.card Pb ≤ Nat.card T := Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hrel := Subgroup.relIndex_mul_card Tb (S' ⊓ Subgroup.normalizer (Tb : Set (X ⧸ N)))
  rw [inf_eq_left.mpr (le_inf hTbS Subgroup.le_normalizer), hcardS, mul_comm] at hrel
  have hrel' : Tb.relIndex (S' ⊓ Subgroup.normalizer (Tb : Set (X ⧸ N))) = Nat.card Pb :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos hrel
  rw [hrel', c.card_T_quotient hN]
  exact hPb

end Core49

omit [Finite X] in
theorem eq_one_of_two_pow_of_odd {G : Type*} [Group G] {M : Subgroup G} {x : G} (hx : x ∈ M)
    (hodd : Odd (Nat.card M)) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card M := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card M) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf x ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

namespace Core49

variable {A T S Q H : Subgroup X} {N : Subgroup X} [N.Normal]

theorem oddCore_quotient (c : Core49 A T S Q H)
    (hN : N = S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
    CFSG.oddCore (A.map (QuotientGroup.mk' N)) = ⊥ := by
  set π := QuotientGroup.mk' N
  set Ab := A.map π
  apply sSup_eq_bot.mpr
  rintro M ⟨hMn, hModd⟩
  set Mx : Subgroup (X ⧸ N) := M.map Ab.subtype
  set Nt : Subgroup X := Mx.comap π ⊓ A
  have hNtn : (Nt.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_right : Nt ≤ A)]
    intro h k hh hk
    refine ⟨?_, A.mul_mem (A.mul_mem hk hh.2) (A.inv_mem hk)⟩
    show π (k * h * k⁻¹) ∈ Mx
    obtain ⟨m, hm, hme⟩ := hh.1
    have hkAb : π k ∈ Ab := Subgroup.mem_map_of_mem π hk
    refine ⟨⟨π k, hkAb⟩ * m * ⟨π k, hkAb⟩⁻¹, hMn.conj_mem m hm _, ?_⟩
    simp only [Subgroup.coe_subtype, map_mul, map_inv]
    rw [show (m : X ⧸ N) = π h from hme]
  rcases Quasisimple.normal_le_center_or_eq_top c.quasisimple (Nt.subgroupOf A) with hle | htop
  · rw [eq_bot_iff]
    intro m hm
    obtain ⟨a, haA, ham⟩ := m.2
    have haNt : a ∈ Nt := ⟨by show π a ∈ Mx; rw [ham]; exact ⟨m, hm, rfl⟩, haA⟩
    have haZ : a ∈ centerOf A := by
      have h1 := hle (Subgroup.mem_subgroupOf.mpr haNt : (⟨a, haA⟩ : A) ∈ Nt.subgroupOf A)
      refine ⟨haA, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨b, hb⟩)
    obtain ⟨k, hk⟩ := c.center_two haZ
    have hmk : m ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← ham, ← map_pow, hk, map_one, Subgroup.coe_one]
    exact Subgroup.mem_bot.mpr (eq_one_of_two_pow_of_odd hm hModd hmk)
  · exfalso
    have hANt : A ≤ Nt := by
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ Nt.subgroupOf A := htop ▸ Subgroup.mem_top _
      exact this
    obtain ⟨r, hrR, hrZ⟩ := Set.not_subset.mp c.R_not_le
    have hrN : r ∉ N := by
      rw [hN]
      exact fun h => hrZ (c.U_le_center h)
    obtain ⟨k, hk⟩ := c.isPGroup_S ⟨r, hrR.1⟩
    have hrM := (hANt hrR.2).1
    obtain ⟨m, hm, hme⟩ := hrM
    have hmk : m ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, show (m : X ⧸ N) = π r from hme, ← map_pow,
        show r ^ (2 ^ k) = 1 from congrArg Subtype.val hk, map_one, Subgroup.coe_one]
    have hm1 := eq_one_of_two_pow_of_odd hm hModd hmk
    apply hrN
    rw [← QuotientGroup.eq_one_iff r]
    have := congrArg Subtype.val hm1
    rw [show (m : X ⧸ N) = π r from hme] at this
    exact this

end Core49

end CFSG.ComponentClassification.AschbacherTheorem3
