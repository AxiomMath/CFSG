module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPrimes
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalCards2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalM11M24
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalExclB
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRank2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure OpenRows : Prop where
  m12_5 : KFactSporLocalRow .M12 5
  m22_5 : KFactSporLocalRow .M22 5
  m22_7 : KFactSporLocalRow .M22 7
  m23_5 : KFactSporLocalRow .M23 5
  m23_7 : KFactSporLocalRow .M23 7
  m24_5 : KFactSporLocalRow .M24 5
  m24_7 : KFactSporLocalRow .M24 7
  j2_7 : KFactSporLocalRow .J2 7
  j3_5 : KFactSporLocalRow .J3 5
  j4_5 : KFactSporLocalRow .J4 5
  j4_7 : KFactSporLocalRow .J4 7
  j4_23 : KFactSporLocalRow .J4 23
  j4_31 : KFactSporLocalRow .J4 31
  j4_43 : KFactSporLocalRow .J4 43
  hs_7 : KFactSporLocalRow .HS 7
  mcl_7 : KFactSporLocalRow .McL 7
  he_17 : KFactSporLocalRow .He 17
  ru_7 : KFactSporLocalRow .Ru 7
  ru_13 : KFactSporLocalRow .Ru 13
  suz_7 : KFactSporLocalRow .Suz 7
  suz_11 : KFactSporLocalRow .Suz 11
  suz_13 : KFactSporLocalRow .Suz 13
  on_5 : KFactSporLocalRow .ONan 5
  on_31 : KFactSporLocalRow .ONan 31
  co2_7 : KFactSporLocalRow .Co2 7
  co2_11 : KFactSporLocalRow .Co2 11
  co2_23 : KFactSporLocalRow .Co2 23
  co3_7 : KFactSporLocalRow .Co3 7
  co3_11 : KFactSporLocalRow .Co3 11
  hn_7 : KFactSporLocalRow .HN 7
  hn_11 : KFactSporLocalRow .HN 11
  ly_7 : KFactSporLocalRow .Ly 7
  ly_31 : KFactSporLocalRow .Ly 31
  th_13 : KFactSporLocalRow .Th 13
  th_31 : KFactSporLocalRow .Th 31

theorem kFactSporLocal_of_rows
    (h : OpenRows) : KFactSporLocal := by
  rw [kFactSporLocal_iff_rows]
  intro s p
  intro A _ _ L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  have hzL : z ∈ L := hK₀L hzK
  cases s
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_M11 A L hL] at hdvd
    rcases primes_M11 hp hp5 hdvd with rfl | rfl
    · exact row_M11_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M11_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_M12 A L hL] at hdvd
    rcases primes_M12 hp hp5 hdvd with rfl | rfl
    · exact h.m12_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M12_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_M22 A L hL] at hdvd
    rcases primes_M22 hp hp5 hdvd with rfl | rfl | rfl
    · exact h.m22_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.m22_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M22_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_M23 A L hL] at hdvd
    rcases primes_M23 hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact h.m23_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.m23_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M23_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M23_23 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_M24 A L hL] at hdvd
    rcases primes_M24 hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact h.m24_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.m24_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M24_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_M24_23 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · exact (false_of_J1 L hL h2).elim
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_J2 A L hL] at hdvd
    rcases primes_J2 hp hp5 hdvd with rfl | rfl
    · exact row_J2_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.j2_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_J3 A L hL] at hdvd
    rcases primes_J3 hp hp5 hdvd with rfl | rfl | rfl
    · exact h.j3_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_J3_17 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_J3_19 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_J4 A L hL] at hdvd
    rcases primes_J4 hp hp5 hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.j4_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.j4_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_J4_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.j4_23 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_J4_29 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.j4_31 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_J4_37 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.j4_43 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_HS A L hL] at hdvd
    rcases primes_HS hp hp5 hdvd with rfl | rfl | rfl
    · exact row_HS_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.hs_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_HS_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_McL A L hL] at hdvd
    rcases primes_McL hp hp5 hdvd with rfl | rfl | rfl
    · exact row_McL_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.mcl_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_McL_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_He A L hL] at hdvd
    rcases primes_He hp hp5 hdvd with rfl | rfl | rfl
    · exact row_He_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_He_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.he_17 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Ru A L hL] at hdvd
    rcases primes_Ru hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact row_Ru_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.ru_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.ru_13 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Ru_29 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Suz A L hL] at hdvd
    rcases primes_Suz hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact row_Suz_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.suz_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.suz_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.suz_13 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_ON A L hL] at hdvd
    rcases primes_ON hp hp5 hdvd with rfl | rfl | rfl | rfl | rfl
    · exact h.on_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_ONan_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_ON_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_ON_19 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.on_31 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · exact (false_of_Co1 L hL hloc).elim
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Co2 A L hL] at hdvd
    rcases primes_Co2 hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact row_Co2_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.co2_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.co2_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.co2_23 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Co3 A L hL] at hdvd
    rcases primes_Co3 hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact row_Co3_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.co3_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.co3_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Co3_23 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · exact (false_of_Fi22 L hL hloc).elim
  · exact (false_of_Fi23 L hL hloc).elim
  · exact (false_of_Fi24Prime L hL hloc).elim
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_HN A L hL] at hdvd
    rcases primes_HN hp hp5 hdvd with rfl | rfl | rfl | rfl
    · exact row_HN_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.hn_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.hn_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_HN_19 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Ly A L hL] at hdvd
    rcases primes_Ly hp hp5 hdvd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact row_Ly_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.ly_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Ly_11 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.ly_31 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Ly_37 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Ly_67 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · have hdvd := prime_dvd_of_orderOf L hzL hz
    rw [hcard_Th A L hL] at hdvd
    rcases primes_Th hp hp5 hdvd with rfl | rfl | rfl | rfl | rfl
    · exact row_Th_5 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Th_7 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.th_13 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact row_Th_19 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
    · exact h.th_31 A L K₀ z hL h2 hloc hp hp5 hrk hz hK₀L hzK hnL hN hcl hy hNN
  · exact (false_of_B L hL hloc).elim
  · exact (false_of_M L hL hloc).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
